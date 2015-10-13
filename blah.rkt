#lang racket

(require racket/generator)

(require "util.rkt" "sets.rkt" "multiset.rkt" "queue.rkt")

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
;;
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
  ;; view-rules is a hash mapping view-pred symbols to sets of view-rules.
  (preds state-rules view-rules)
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

;; a transition is a state rule to apply plus a substitution.
;; a substition is a hash mapping the vars of the state rule to ground terms.
(struct transition (state-rule substitution) #:transparent)

;; internal is a hash from symbols to multisets of tuples.
;; inbox & outbox are queues of head-tuples
(struct state (internal inbox outbox) #:transparent)


;; Views and querying.

;; A "view cache" is a mutable hash mapping view-pred symbols to sets of tuples.
(define (make-cache) (make-hash))

;; tries to fire a state rule.
;; returns a set of substitutions by which the rule can fire.
;; may update cache.
;; (empty if it does not fire.)
(define (fire prog s cache rule)
  (match-define (state-rule _ pre post side) rule)
  (satisfy-all (append pre side)))

;; returns a set of substitutions which satisfy the conditions.
;; the conditions may have any kinds of predicates.
;; may update cache.
(define (satisfy-all prog s cache vars conds)
  (define substs (set (hash)))
  (for ([c conds]
        ;; early exit if we're unsatisfiable
        #:unless (set-empty? substs))
    (set! substs (satisfy-extend prog s cache vars c substs)))
  substs)

;; Tries to satisfy `cnd' in a way that extends the substitution-set `substs'.
;; Returns the updated substitution-set (which will be empty if unsatisfiable).
;; May update cache.
(define (satisfy-extend prog s cache vars cnd substs)
  (join-substs vars substs (satisfy prog s cache vars cnd)))

;; Does a natural join on two substitution-sets.
(define (join-substs vars subs1 subs2)
  (let*/set ([s1 subs1] [s2 subs2])
    (match-substs vars s1 s2)))

;; Finds all substitutions satisfying a single condition.
;; May update cache.
(define (satisfy prog s cache vars cnd)
  (match-define (cons pred args) cnd)
  (match-define (state internal-state inbox outbox) s)
  (define tuples
    (match (hash-ref (program-preds prog) pred)
      ['view (hash-ref cache pred
               (lambda () (compute-view prog s cache pred)))]
      ['state (hash-ref internal-state pred (set))]
      ['input (if (queue-empty? inbox)
                (set)
                ;; use of queue-peek is asymptotically inefficient :(
                (set (queue-peek inbox)))]
      ['output (error "cannot satisfy output predicates")]))
  (let*/set ([tuple tuples])
    (match-arguments vars args tuple)))

;; matches an argument against a concrete tuple, producing a set of
;; substitutions. the set is either empty or a singleton.
(define (match-arguments vars args tuple)
  (assert! (= (length args) (length tuple)))
  (let/ec return
    (define h (make-hash))
    (for ([a args] [v tuple])
      (cond
        [(var? a) (hash-set! h a v)]
        [(not (equal? a v)) (return (set))]))
    (set (freeze-hash h))))

;; matches two substitutions against one another, producing a set of joined
;; substitutions (either empty or a singleton).
(define (match-substs vars s1 s2)
  (let/ec return
    (set (hash-union-with s1 s2 (lambda (_ _) (return (set)))))))

;; Computes the entirety of a given view.
;; May update cache.
;; Returns view-tuples.
(define (compute-view prog s cache pred)
  (match-define (program preds state-rules view-rules) prog)
  (assert! (equal? 'view (hash-ref preds pred #f)))
  (define rules (hash-ref view-rules pred (set)))
  (error "unimplemented")
  ;; (for ([r rules])
  ;;   )
  )


;; produces a set of transitions that fire.
(define (transitions prog s)
  (define cache (make-cache))
  (for*/set ([rule (program-state-rules prog)]
             [subst (fire prog s cache rule)])
    (transition rule subst)))

(define (apply-transition program state transition)
  (error "unimplemented"))

;; applies transitions until there are no more to apply.
;; currently errors if there is any nondeterminism.
;; FIXME: think harder about nondeterminism.
;;
;; returns: (values new-state list-of-transitions)
(define (quiesce program s)
  (let loop ([s s]
             [txns '()])
    (define outs (transitions program s))
    (match (set-count outs)
      [0 (values s (reverse txns))]
      [1 (let ([txn (set-first outs)])
           (loop (apply-transition program s txn) (cons txn txns)))]
      [_ (error "multiple transitions apply")])))


;; returns: new-state
(define (send message program st)
  (match-define (state l i o) st)
  (state l (queue-push message i) o))

;; returns: (values new-state message)
(define (recv program st [on-empty (lambda () (error "no message to recv"))])
  (match-define (state l i o) st)
  (define-values (new-o msg) (queue-pop o on-empty))
  (values (state l i new-o) msg))

;; returns: (values new-state message-list)
;; message-list has most recent output message first.
(define (recv-all program st)
  (match-define (state l i o) st)
  (values (state l i empty-queue) (queue->list o)))
