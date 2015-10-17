#lang racket

(require "util.rkt" "sets.rkt" "dataflow.rkt")


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


;;; ---------- COMPILER: DATALOG -> DATAFLOW ----------
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

;;; The node types.
(define (pred-node pred clause-ids)
  (define/contract (func vals) eval-func/c
    (set-unions
      (for/list ([c clause-ids])
        (hash-ref vals c))))
  ;; TODO?: more optimized equality function? for example, since we're
  ;; currently monotonic, we know that if our size is the same, we haven't
  ;; changed!
  (node func equal?))

(define (clause-node c)
  (match-define (clause name args body) c)
  (define/contract (func vals) eval-func/c
    (define substs
      (foldl join-substs (set (hash))
        (for/list ([e body])
          (eval-expr vals e))))
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
(define (eval-expr vals e)
  (match-define (e-pred pred args) e)
  (define tuples (hash-ref vals pred))
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
  (let*/set ([s1 subs1] [s2 subs2])
    (match-substs s1 s2)))

;; matches two substitutions against one another, producing a set of joined
;; substitutions (either empty or a singleton).
(define/contract (match-substs s1 s2)
  (-> hash? hash? set?)
  (let/ec return
    (define (check a b)
      (if (equal? a b) a
        (return (set))))
    (set (hash-union-with s1 s2 check))))


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

(define s #f)
(define (reset)
  (set! s (make-state g (const (set)))))
(reset)

(define (test [s s])
  (quiesce! g s)
  (set->list (hash-ref (state-values s) 'ancestor)))
