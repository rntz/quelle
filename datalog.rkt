#lang racket

(require "util.rkt" "sets.rkt")

(define (unimplemented) (error "Unimplemented!"))


;;; ---------- DATALOG ----------
;; args: list of terms
;; body: list of exprs
(struct clause (name args body) #:transparent)

(enum expr
  ;; (e-conj exprs) ;; TODO?
  ;; (e-disj exprs) ;; TODO
  ;;(e-not expr) ;; TODO
  (e-pred name args))

(enum term
  (t-var name)
  (t-lit value))

(define (terms-vars ts) (set-unions (map term-vars ts)))
(define (term-vars t)
  (match t
    [(t-var x) (set x)]
    [(t-lit _) (set)]))

(define (exprs-vars es) (set-unions (map expr-vars es)))
(define (expr-vars e)
  (match e
    ;; [(or (e-disj es) (e-conj es)) (exprs-vars es)]
    [(e-pred _ as) (terms-vars as)]))

;; Datalog clause well-formedness rule: all variables in `args' must appear at
;; least once in `body' in positive position. (It is OK for that positive
;; position to be a recursive call.)
;;
;; (TODO: there are more rules once we introduce negation)
;;
;; foo(X) :- not(bar(X)). -- is this OK? no, because infinitely many such Xs.
(define (clause-vars-ok? c)
  (match-define (clause name args body) c)
  (subset? (terms-vars args) (exprs-vars body)))

(define clause-ok? clause-vars-ok?)

;; a db is a hash mapping names to lists of clauses.
(define db? (hash/c symbol? (listof clause?)))


;;; ---------- PARSER INTO DATALOG ----------
(define (parse-prog clauses)
  (define db (make-hash))
  (for ([c (map parse-clause clauses)])
    (hash-update! db (clause-name c)
      (lambda (v) (cons c v))
      (lambda () '())))
  db)

(define (parse-clause c)
  (match c
    [`((,name . ,args) . ,body)
      (clause name (map parse-term args) (map parse-expr body))]))

(define (parse-term a)
  (match a
    [(? symbol?) (t-var a)]
    [`',x (t-lit x)]
    [_ (t-lit a)]))

(define (parse-expr e)
  (match e
    [`(,name . ,args) (e-pred name (map parse-term args))]))


;;; ---------- DATAFLOW GRAPHS ----------

;; nodes: maps node ids to node structures.
;; depends: maps node id N to the node ids of nodes it depends on.
;; dependees: maps node id N to the node ids of nodes depending on N.
(struct graph (nodes depends dependees) #:transparent)

;; func: function that updates the node.
;; same: function that determines if node value is unchanged.
;; depends: node IDs this node depends on.
(struct node (func same) #:transparent)

;;; A state of the dataflow graph.
(struct state
  ;; dirty is a mutable set of node ids.
  ;; tuples is a mutable hash from node ids to tuple-sets.
  (dirty tuples)
  #:transparent)

;; A node function takes the state of the world and produces a new value for the
;; node. It must *not* mutate the state of the world.
(define node-func/c (-> state? (set/c any/c)))
;; A same function takes the old and new values and determines if there's
;; been a change.
(define same-func/c (-> any/c any/c boolean?))


;;; ---------- DATAFLOW GRAPH INTERPRETER ----------
(define/contract (make-state graph)
  (-> graph? state?)
  (define node-ids (hash-keys (graph-nodes graph)))
  (state
    ;; initially everything's dirty
    (list->mutable-set node-ids)
    ;; ... and empty
    (make-hash (for/list ([n node-ids]) (cons n (set))))))

;; runs nodes in graph until all nodes are clean.
(define (quiesce g s)
  (define dirty (state-dirty s))
  (unless (set-empty? dirty)
    ;; pick a node "at random" & run it.
    (run-node! g s (set-first dirty))
    ;; keep going.
    (quiesce g s)))

;; re-runs node unconditionally.
;; does not check whether node is dirty.
;; clears node's dirty state and dirties its dependees as appropriate.
(define (run-node! g s node-id)
  (printf "RUN: ~a\n" node-id)
  (match-define (graph nodes depends dependees) g)
  (match-define (state dirty tuples) s)
  (match-define (node func same) (hash-ref nodes node-id))
  (define old-tuples (hash-ref tuples node-id (lambda () (set))))
  (define new-tuples (func s))
  ;; if we same, we have work to do.
  (unless (same old-tuples new-tuples)
    (printf "  ~a changed: ~v\n" node-id (set-subtract new-tuples old-tuples))
    ;; update our value & dirty our dependees
    (hash-set! tuples node-id new-tuples)
    (set-union! dirty (hash-ref dependees node-id)))
  ;; clear our node
  (set-remove! dirty node-id))

;;; The node types.
(define (pred-node pred clause-ids)
  (define/contract (func s) node-func/c
    (set-unions
      (for/list ([c clause-ids])
        (hash-ref (state-tuples s) c))))
  ;; TODO?: more optimized equality function? for example, since we're
  ;; currently monotonic, we know that if our size is the same, we haven't
  ;; changed!
  (node func equal?))

(define (clause-node c)
  (match-define (clause name args body) c)
  (define/contract (func s) node-func/c
    (define substs
      (foldl join-substs (set (hash))
        (for/list ([e body])
          (eval-expr s e))))
    ;; now extract the tuples from the substitution.
    ;; this is a projection, essentially.
    (for/set ([s substs])
      (for/list ([a args])
        (match a
          [(t-var v) (hash-ref s v)]
          [(t-lit v) v]))))
  ;; TODO?: more optimized equality function? see above.
  (node func equal?))

;;; Evaluating expressions
(define (eval-expr s e)
  (match-define (e-pred pred args) e)
  (define tuples (hash-ref (state-tuples s) pred))
  ;; Filter & project.
  (let*/set ([tuple tuples])
    (extract-args args tuple)))

;; matches a tuple against an argument
;; combines filtering & projecting
(define (extract-args args tuple)
  (assert! (= (length args) (length tuple)))
  (let/ec return
    (define (fail-unless x) (unless x (return (set))))
    (define h (make-hash))
    (for ([a args] [v tuple])
      (match a
        [(t-var x) (hash-set! h x v)]
        [(t-lit x) (fail-unless (equal? x v))]))
    (set (freeze-hash h))))

;; Does a natural join on two substitution-sets.
(define (join-substs subs1 subs2)
  (printf "joining: ~v\nwith:    ~v\n" subs1 subs2)
  (define r
    (let*/set ([s1 subs1] [s2 subs2])
      (match-substs s1 s2)))
  (printf "result: ~v\n\n" r)
  r)

;; matches two substitutions against one another, producing a set of joined
;; substitutions (either empty or a singleton).
(define/contract (match-substs s1 s2)
  (-> hash? hash? set?)
  (let/ec return
    (define (check a b)
      (if (equal? a b) a
        (return (set))))
    (set (hash-union-with s1 s2 check))))


;;; ---------- COMPILER, DATALOG TO DATAFLOW GRAPHS ----------
;; We assign node ids as follows:
;; - a predicate's node id is simply its name.
;; - clauses get gensym'ed node ids.
(define (compile-prog db)
  (define nodes (make-hash))
  (define depends (make-hash))
  (for ([(pred clauses) db])
    (define clause-ids
      (for/set ([c clauses])
        (compile-clause nodes depends c)))
    (hash-set! nodes pred (pred-node pred clause-ids))
    (hash-set! depends pred clause-ids))
  (graph (freeze-hash nodes) (freeze-hash depends) (reverse-graph depends)))

(define (compile-clause nodes depends c)
  (define clause-id (gensym (clause-name c)))
  (define pred-ids (map e-pred-name (clause-body c)))
  (hash-set! depends clause-id pred-ids)
  (hash-set! nodes clause-id (clause-node c))
  clause-id)

;; reverses an adjacency-set representation of a graph
(define/contract (reverse-graph g)
  (->
    (hash/c any/c (set/c any/c #:kind 'dont-care) #:immutable 'dont-care)
    (hash/c any/c (set/c any/c #:kind 'dont-care) #:immutable 'dont-care))
  (define reversed (make-hash))
  (for ([(k vs) g])
    (for ([v vs])
      (hash-update! reversed v
        (lambda (x) (set-add! x k) x)
        (lambda () (mutable-set)))))
  ;; mutability police! freeze!
  (for/hash ([(k v) reversed])
    (values k (freeze-set v))))


;;; test case
(define prog
  '(((person 'constable))
    ((person 'harper))
    ((person 'arbob))
    ((parent 'constable 'harper))
    ((parent 'harper 'arbob))
    ((ancestor X X) (person X))
    ((ancestor X Z) (parent X Y) (ancestor Y Z))))

(define p (parse-prog prog))
(define g (compile-prog p))
(define s (make-state g))
(define (reset) (set! s (make-state g)))
(define (test [s s])
  (quiesce g s)
  (set->list (hash-ref (state-tuples s) 'ancestor)))
