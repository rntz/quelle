#lang racket

(require "util.rkt" "sets.rkt" "multiset.rkt" "queue.rkt"
  (prefix-in flow: "dataflow.rkt"))

(provide (all-defined-out))

;;; NOTES
;;
;; 1. Will need to throw away state and re-generate on every time-step. This is
;; because recursive dataflow programs are effectively stateful, and while they
;; are still - I'm pretty sure - monotonic, if I ever *remove* any tuples, all
;; bets are off. Since I'm depending on linear state, which might remove tuples,
;; the safe thing is to throw out everything.
;;
;; TODO: Figure out more optimized ways to handle this. In general, the problem
;; is: non-monotonicity + recursion + incrementality = hard.
;;
;; 2. Moreover, it's not clear how best to handle "external inputs" into a
;; dataflow program. Currently I'll have to do this by hacking them in as
;; "initial states" of certain predicates. The update functions for these
;; predicates will be nops ("get & return my current value").
;;
;; 3. It's not clear when two state transitions are "identical". This question
;; is relevant for (a) displaying transitions to users during debugging; and (b)
;; determining whether we are taking a nondeterministic transition or not.
;;
;; The coarsest, and perhaps most natural, reasonable equality is: two
;; transitions are equal if they result in equal states.
;;
;; However, we can also distinguish transitions by:
;;
;; - which state rule fired. two different rules may lead to the same
;;   next-state in various ways. TODO: examples.
;;
;; - what variable substitution the transition involved. if a variable occurs
;;   only in side-conditions, for example, there may be redundant transitions to
;;   the same state.
;;
;; - whether a fact was removed and re-added, or merely left alone. for example,
;; {a,b} --> {a,b,c} may happen due to the rule:
;;
;;    b -o b,c.
;;
;; which uses and re-creates b, or by the rule:
;;
;;    {} -o c when b.
;;
;; which merely has b as a side-condition.
;;
;; Currently we use all of the above in our definition of transition, making for
;; a very fine-grained notion of equality of transition.

;; TODO: think carefully about semantics of input & output messages. should they
;; be multisets, not queues? that would be more in line with linear logic, and
;; could always tag them with unique ids to recover time ordering. otoh,
;; provokes nondeterminism.
;;
;; basically I need to think more about the "temporal"/timing aspect of this
;; whole thing. what's a time-step? are there multiple notions of time-step?


;; ---------- TYPES ----------
;; A tuple is just a list of values.
;; A head-tuple is a list (pred term1 term2 ... termn).
;; A condition is a list (pred arg1 arg2 ... argn).
(define tuple/c (listof any/c))
(define condition/c (cons/c symbol? tuple/c))
(define substitution/c (hash/c symbol? any/c))

;; An argument is either a term or a variable.
;; A variable is a symbol that starts uppercase.
;; A term is anything else.
(define (var? x)
  (and (symbol? x)
    (let ([n (symbol->string x)])
      (and (> 0 (string-length n)) (char-upper-case? (string-ref n 0))))))

(struct program
  ;; preds is a hash from symbols to one of 'view, 'state, 'input, or 'output.
  ;; state-rules is a set of state-rules.
  ;; views is a hash mapping view-pred symbols to sets of view-rules.
  ;; every view pred must have an entry in views.
  (preds state-rules views)
  #:transparent)

;; a linear "state transition" rule.
;; pre, post, and side are all lists of conditions.
;; pre & post are conditions w/ linear predicates (state, input, or output)
;; input predicates may only appear in pre, outputs may only appear in post.
;; side conditions may have any kind of predicate.
;;
;; the variables in `post' must all be in `pre' or `conditions'.
(struct state-rule (vars pre post side) #:transparent)

;; a datalog-style "view" rule.
;; head is a condition with a view predicate.
;; body is a list of conditions, of any kind.
;; the variables in head must all be present in body.
(struct view-rule (vars head body) #:transparent)

;; a transition describes how to update our state.
;; rule is the state-rule being fired.
;; subst is a hash mapping the vars of rule to ground terms.
;; pre is a multiset of facts to be removed.
;; post is a multiset of facts to be added.
(struct transition (rule subst pre post)
  #:transparent)

;; our state is a hash from predicate names to multisets of tuples.
(define state? hash?)
(define state/c (hash/c symbol? multiset? #:immutable #t))

;; TODO: well-formedness checking for rules, transitions, etc.


;;; ---------- UTILITIES ----------
(define (pred-type prog p) (hash-ref (program-preds prog) p))
(define (pred-input? prog p) (equal? 'input (pred-type prog p)))
(define (pred-output? prog p) (equal? 'output (pred-type prog p)))
(define (pred-internal? prog p) (equal? 'state (pred-type prog p)))

(define (preds-of-kind kind prog)
  (for/set ([(p k) (program-preds prog)] #:when (equal? k kind)) p))

(define input-preds (curry preds-of-kind 'input))
(define output-preds (curry preds-of-kind 'output))
(define internal-preds (curry preds-of-kind 'state))
(define view-preds (curry preds-of-kind 'view))

;; returns subhash of state for input predicates
(define (state-inputs prog s) (hash-filter-keys (curry pred-input? prog) s))
(define (state-output prog s) (hash-filter-keys (curry pred-output? prog) s))
(define (state-internal prog s)
  (hash-filter-keys (curry pred-internal? prog) s))

(define (substate? s1 s2)
  (for/and ([(k v) s1])
    (submultiset? v (hash-ref s2 k (lambda () (multiset))))))

(define (state-empty? s) (substate? s (hash)))

(define/contract (instantiate-conditions subst conds)
  (-> substitution/c (listof condition/c) state/c)
  (define h (make-hash))
  (for ([c conds])
    (match-define (cons pred args) c)
    (hash-update! h pred
      (lambda (x) (multiset-add x (args->tuple subst args)))
      (lambda () (multiset))))
  (freeze-hash h))


;;; ---------- COMPILER: QUELLE -> DATAFLOW ----------
;; Every predicate gets a node named by it.
;; Each view-rule gets a node named by a gensym.
(define (prog->graph prog)
  (match-define (program preds state-rules views) prog)
  (define nodes (make-hash))
  (define depends (make-hash))
  (for ([(pred kind) preds])
    (match kind
      ['view (compile-view nodes depends pred (hash-ref views pred))]
      [(or 'state 'input) (add-dummy-node nodes depends pred)]))
  (flow:graph
    (freeze-hash nodes)
    (freeze-hash depends)
    (flow:reverse-graph depends)))

;; this is a minor hack.
(define (add-dummy-node nodes depends pred)
  (define/contract (eval-func vals) flow:eval-func/c
    (hash-ref vals pred))
  ;; TODO?: equal? here could be (const #t), if it matters.
  (hash-set! nodes pred (flow:node eval-func equal?))
  (hash-set! depends pred (set)))

(define (compile-view nodes depends pred rules)
  (define rule-ids
    (for/list ([r rules])
      (compile-view-rule nodes depends r)))
  (define/contract (eval-func vals) flow:eval-func/c
    (set-unions (map (curry hash-ref vals) rule-ids)))
  ;; TODO?: faster same-func than equal?.
  (hash-set! nodes pred (flow:node eval-func equal?))
  (hash-set! depends pred (list->set rule-ids)))

(define (compile-view-rule nodes depends rule)
  (match-define (view-rule vars (cons pred args) body) rule)
  (define rule-id (gensym pred))
  (define/contract (eval-func vals) flow:eval-func/c
    (for/set ([subst (satisfy-all vals body)])
      (args->tuple subst args)))
  ;; TODO?: more efficient same-func than equal?.
  (hash-set! nodes rule-id (flow:node eval-func equal?))
  (hash-set! depends rule-id (list->set (map car body)))
  rule-id)


;;; ---------- RUNTIME ----------
;; Finds all substitutions satisfying all conditions.
(define (satisfy-all vals conds)
  (define substs (set (hash)))
  (for ([c conds]
        ;; early exit if we're unsatisfiable
        #:unless (set-empty? substs))
    (set! substs (join substs (satisfy vals c))))
  substs)

;; Finds all substitutions satisfying a single condition.
(define (satisfy vals cnd)
  (match-define (cons pred args) cnd)
  (let*/set ([tuple (hash-ref vals pred)])
    (match-arguments args tuple)))

;; Does a natural join on two substitution-sets.
(define (join subs1 subs2)
  (let*/set ([s1 subs1] [s2 subs2])
    (join-substs s1 s2)))

;; Matches two substitutions against one another, producing a set of joined
;; substitutions (either empty or a singleton).
(define (join-substs s1 s2)
  (let/ec return
    (define (check a b)
      (if (equal? a b) a
        (return (set))))
    (set (hash-union-with s1 s2 check))))

;; Matches an argument against a concrete tuple, producing a set of
;; substitutions. The set is either empty or a singleton.
(define (match-arguments vars args tuple)
  (assert! (= (length args) (length tuple)))
  (let/ec return
    (define h (make-hash))
    (for ([a args] [v tuple])
      (cond
        [(var? a) (hash-set! h a v)]
        [(not (equal? a v)) (return (set))]))
    (set (freeze-hash h))))

(define (args->tuple subst args)
  (for/list ([a args])
    (cond
      [(var? a) (hash-ref subst a)]
      [#t a])))


;;; ---------- FINDING TRANSITIONS ----------
;; TODO?: functions here assume that our dataflow graph has been run to
;; saturation! instead, inline on-demand dataflow graph evaluation with our
;; runtime, for better performance?
;;
;; NB. must distinguish between runtime for dataflow graph (which has to just
;; use the current graph values) and runtime for finding state transition (which
;; can ask the dataflow graph to compute on-demand).

;; Produces the set of transitions that fire.
;; HEAVYWEIGHT OPERATION. DO NOT CALL REPEATEDLY.
;; TODO?: have this return a generator/stream?
(define (transitions prog s)
  (match-define (program preds state-rules views) prog)

  ;; set up a flow graph representing us
  (define graph (prog->graph prog))
  (define (init-value node-id)
    (match (hash-ref preds node-id #f)
      ;; NB. multiset->set loses information. This is a design flaw. See
      ;; "Dependence of view rules on state predicates" in ideas.org for plan to
      ;; fix it.
      [(or 'state 'input) (multiset->set (hash-ref s node-id))]
      ['output (error "outputs should not get graph nodes")]
      [_ (set)]))
  (define flow-state (flow:make-state graph init-value))

  ;; quiesce the flow graph state
  (flow:quiesce! graph flow-state)

  ;; use the flow graph to figure out which state-rules fire
  (let*/set ([rule state-rules])
    (fire s rule (flow:state-values flow-state))))

;; Applies a state rule, returning a set of transitions by which the rule can
;; fire. (Empty if it does not fire.)
(define (fire s rule vals)
  (match-define (state-rule _ pre post side) rule)
  ;; first, find all substs satisfying pre- and side-conditions, ignoring
  ;; resource multiplicity constraints.
  (define substs (satisfy-all vals (append pre side)))
  ;; now, filter down to ones which satisfy multiplicity constraints.
  (let*/set ([subst substs])
    (define used (instantiate-conditions subst pre))
    (if (not (substate? used s))
      ;; not enough resources to fire :c
      (set)
      ;; fire!
      (set (transition rule subst used (instantiate-conditions subst post))))))


;;; Other operations
;; applies transitions until there are no more to apply.
;; currently errors if there is any nondeterminism.
;; FIXME: think harder about nondeterminism.
;;
;; returns: (values new-state list-of-transitions)
(define (quiesce! prog s)
  (let loop ([s s]
             [txns '()])
    (define outs (transitions prog s))
    (match (set-count outs)
      [0 (values s (reverse txns))]
      [1 (let ([txn (set-first outs)])
           (loop (apply-transition s txn) (cons txn txns)))]
      [_ (error "multiple transitions apply")])))

(define (apply-transition s txn)
  (match-define (transition rule subst pre post) txn)
  (assert! (substate? pre s))
  (assert! (for/and ([pred (hash-keys post)])
             (hash-has-key? s pred)))
  (for/hash ([(pred tuples) s])
    (when (hash-has-key? pre pred)
      (set! tuples (multiset-subtract tuples (hash-ref pre pred))))
    (when (hash-has-key? post pred)
      (set! tuples (multiset-union tuples (hash-ref post pred))))
    (values pred tuples)))


;;; Dealing with inputs & outputs.

;; inputs: hash-multiset of new inputs.
;; returns: new-state
(define/contract (send program s inputs)
  (program? state/c state/c . -> . state/c)
  (assert! (subset? (hash-keys inputs) (input-preds program)))
  (unless (state-empty? (state-inputs s))
    (error "state already has inputs!"))
  (hash-union-with s inputs multiset-union))

;; returns: (values new-state messages)
(define/contract (recv prog s)
  (program? state/c . -> . (values state/c state/c))
  (unless (state-empty? (state-inputs prog s))
    (error "receiving from state with fresh inputs"))
  (define new-s (hash-filter-keys (lambda (p) (not (pred-output? prog p))) s))
  (values new-s (state-output prog s)))
