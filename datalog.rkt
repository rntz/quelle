#lang racket

(require "util.rkt" "sets.rkt")

(define (unimplemented) (error "Unimplemented!"))

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


;;; Interpreter.
(struct pred-state (done tuples ;; new-tuples
                     )
  #:transparent #:mutable)

;; (define pred-state-empty (state #t (set) (set)))
;; (fn pred-state-union
;;   [() pred-state-empty]
;;   [(x) x]
;;   [((state d1 t1 nt1) (state d2 t2 nt2))
;;     (state (and d1 d2) (set-union t1 t2) (set-union nt1 nt2))]
;;   [(x . xs) (foldl pred-state-union x xs)])

(define state/c (hash/c symbol? pred-state?))
(define (make-state pred-names)
  (for/hash ([p pred-names])
    (values p (pred-state #f (mutable-set)))))

(define (state-ref state pred) (hash-ref state pred))
(define (state-done? state pred) (pred-state-done (state-ref state pred)))
(define (state-tuples state pred) (pred-state-tuples (state-ref state pred)))
;; (define (state-new-tuples state pred)
;;   (pred-state-new-tuples (state-ref state name)))

;; returns (values done tuples)
(define (eval-pred db state pred-stack pred)
  (if (member pred pred-stack)
    ;; visiting this predicate recursively.
    (values #f (state-tuples state pred))
    ;; visiting this predicate normally.
    (let ([our-state (state-ref state pred)])
      ;; if it isn't already done, (re-)run it
      (unless (pred-state-done our-state)
        (run-pred! db state pred-stack pred our-state))
      (values (pred-state-done our-state) (pred-state-tuples our-state)))))

(define (run-pred! db state pred-stack pred our-state)
  (assert! (not (pred-state-done our-state)))
  (assert! (not (member pred pred-stack)))
  (define will-be-done #t)
  (define our-tuples (pred-state-tuples our-state))
  (set! pred-stack (cons pred pred-stack))
  ;; calculate the predicate's tuples.
  (for ([c (hash-ref db pred)]) ;; for each clause
    (define-values (clause-done clause-tuples)
      (eval-clause db state pred-stack c))
    (unless clause-done (set! will-be-done #f))
    (set-union! our-tuples clause-tuples))
  (set-pred-state-done! our-state will-be-done))

(define (eval-clause db state pred-stack c)
  (match-define (clause _ args body) c)
  (define-values (done hashes) (eval-conj db state pred-stack body))
  (values done
          (for/set ([h hashes])
            (for/list ([a args])
              (match a
                [(t-var v) (hash-ref h v)]
                [(t-lit v) v])))))

;; my kingdom for a monad!
(define (eval-conj db state pred-stack body)
  (define (j xs)
    (foldl join-substs (set (hash)) xs))
  (eval-exprs db state pred-stack j body))

;; Does a natural join on two substitution-sets.
(define (join-substs subs1 subs2)
  ;; (printf "joining: ~v\nwith:    ~v\n" subs1 subs2)
  (define r
    (let*/set ([s1 subs1] [s2 subs2])
      (match-substs s1 s2)))
  ;; (printf "result: ~v\n\n" r)
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

(define (eval-exprs db state pred-stack f es)
  (define ok-so-far #t)
  (define d
    (for/list ([e es])
      (define-values (ok s) (eval-expr db state pred-stack e))
      (unless ok (set! ok-so-far #f))
      s))
  (values ok-so-far (f d)))

(define (eval-expr db state pred-stack e)
  (match e
    ;; [(e-disj es) (eval-exprs set-unions es)]
    ;; FIXME: doesn't handle empty intersections properly.
    ;; [(e-conj es) (eval-exprs set-intersects es)]
    [(e-pred name args)
      (define-values (ok tuples)
        (eval-pred db state pred-stack name))
      (values ok
        (let*/set ([t tuples])
          (extract-args args t)))]))

;; combines filtering & projecting
(define (extract-args args tuple)
  (let/ec return
    (define (fail-unless x) (unless x (return (set))))
    (set (let ([h (make-hash)])
           (assert! (= (length args) (length tuple)))
           (for ([a args] [t tuple])
             (match* (a t)
               [((t-lit x) y) (fail-unless (equal? x y))]
               [((t-var v) x) (hash-set! h v x)]))
           h))))


;;; Parser
(define (parse-prog clauses)
  (define db (make-hash))
  (for ([c (map parse-clause clauses)])
    (hash-update! db (clause-name c)
      (lambda (v) (cons c v))
      (lambda () (list c))))
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
