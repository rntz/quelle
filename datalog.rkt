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
(struct state (old-tuples new-tuples) #:transparent)

(define (make-state preds)
  (state
    (for/hash ([p preds]) (values p (set)))
    (for/hash ([p preds]) (values p (mutable-set)))))

;; unions the new-tuples into the old-tuples and clears the new-tuples.
;; functional; produces a new state object w/o changing the old.
;; idempotent; applying twice is same as applying once.
(define (flip-state s)
  (match-define (state olds news) s)
  (state
    (hash-union-with olds news set-union)
    (for/hash ([(k _) news]) (values k (mutable-set)))))

(define (eval-pred db s stack pred)
  (match-define (state old-tuples new-tuples) s)
  (define olds (hash-ref old-tuples pred))
  (define news (hash-ref new-tuples pred))
  (if (member pred stack)
    ;; visiting recursively, just grab old values.
    olds
    ;; visiting normally.
    (let ([stack (cons pred stack)])
      (for ([c (hash-ref db pred)])
        (set-union! news (eval-clause db s stack c)))
      (set-union olds news))))

(define (eval-clause db s stack c)
  (match-define (clause _ args body) c)
  (define hashes (eval-conj db s stack body))
  (for/set ([h hashes])
    (for/list ([a args])
      (match a
        [(t-var v) (hash-ref h v)]
        [(t-lit v) v]))))

(define (eval-conj db s stack body)
  (foldl join-substs (set (hash))
    (for/list ([e body])
      (eval-expr db s stack e))))

(define (eval-expr db s stack e)
  (match-define (e-pred name args) e)
  (let*/set ([t (eval-pred db s stack name)])
    (extract-args args t)))

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


;;; Parser
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


;;; test case
;; person
(define prog
  '(((person 'constable))
    ((person 'harper))
    ((person 'arbob))
    ((parent 'constable 'harper))
    ((parent 'harper 'arbob))
    ((ancestor X X) (person X))
    ((ancestor X Z) (parent X Y) (ancestor Y Z))))

(define p (parse-prog prog))
(define s (make-state '(person parent ancestor)))
(define (test [s s]) (eval-pred p s '() 'ancestor))
