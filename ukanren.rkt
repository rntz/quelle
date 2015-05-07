#lang racket

(require "util.rkt")

(provide
  (struct-out Var)
  empty-state
  ground?
  comp/c goal/c
  c/pure c/join c/map1 c/map c/seq c/bind alt c/fresh
  ok fail fresh conj disj zzz condo trace
  run-goal solve
  equalo
  )

;; A term is:
;; - a Var
;; - a cons of two terms
;; - an atom (any other data type)
(struct Var (id name) #:transparent)

;; A uKanren state is:
;; - the next var id to allocate.
;; - a substitution mapping from variable ids to terms.
(struct State (next-id subst) #:transparent)

(define empty-state (State 0 (hash)))

(define (extend var term sub)
  (hash-set sub (Var-id var) term))

;; A term is ground if it contains no variables.
(define/match (ground? t)
  [((cons x y)) (and (ground? x) (ground? y))]
  [((? Var?)) #f]
  [(_) #t])

;; Replaces all bound variables in a term with their bindings.
;;
;; TODO: path compression!
;; first, would need to make all things go through walk.
(define (walk t subst)
  (match t
    [(cons x y) (cons (walk x subst) (walk y subst))]
    [(Var x _) #:when (hash-has-key? subst x)
      (walk (hash-ref subst x) subst)]
    [_ t]))


;; A uKanren computation of type A is a procedure of type:
;;
;;     State -> stream (Got A)
;;
;; or, if A is void, may also be a boolean (#t or #f).
;;
;; A stream of As is either:
;; - null
;; - (cons A (stream A))
;; - () -> stream A
;;
(struct Got (value state) #:transparent)

(define (comp/c A)
  (define c (-> State? (stream/c (got/c A))))
  (if (eq? void? A)                     ;hack
    (or/c c boolean?)
    c))
(define (got/c A) (struct/c Got A State?))
(define (stream/c A)
  (or/c
    null?
    (cons/c A (recursive-contract (stream/c A)))
    (-> (recursive-contract (stream/c A)))))

;; A goal is a computation of type void (i.e. unit)
(define goal/c (comp/c void?))


;; gots form a functor, applicative, monad
(define (got/map1 f x)
  (match x [(Got v st) (Got (f v) st)]))


;; Streams form a functor, an applicative, an alternative, and a monad.
(define (s/pure x) (list x))

(define (s/mapper f s)
  (match s
    ['() '()]
    [(cons x xs) (f x (s/mapper f xs))]
    [(? procedure?) (lambda () (s/mapper f (s)))]))

(define (s/join s) (s/mapper s/alt s))
(define (s/map1 f s) (s/mapper (lambda (x s) (cons (f x) s)) s))
(define (s/bind s f) (s/join (s/map1 f s)))

(define (s/seq ss)
  (let loop ([acc '()] [ss ss])
    (match ss
      ['() (s/pure (reverse acc))]
      [(cons s ss)
        (s/bind s (lambda (x) (loop (cons x acc) ss)))])))

(define (s/list . ss) (s/seq ss))

(define (s/map f . ss)
  (apply s/map1 (curry apply f) (s/seq ss)))

(define s/empty '())

(fn s/alt
  [() s/empty]
  [(s) s]
  ;; 2-argument
  [('() b) b]
  [((cons a as) b) (cons a (s/alt b as))]
  [((? procedure? a) b) (lambda () (s/alt b (a)))]
  ;; 3-argument or more
  [(a b . cs) (s/alt a (apply s/alt b cs))])

;;; deduplicating streams
(define (s/dedup s [guaranteed #t])
  (define found-so-far (if guaranteed (mutable-set) (weak-set)))
  (define/match (dedup x)
    [('()) '()]
    [((cons x xs))
      (if (set-add!ed? found-so-far x)
        (cons x (dedup xs))
        (dedup xs))]
    [((? procedure? f)) (lambda () (dedup (f)))])
  (dedup s))

(define (set-add!ed? st v)
  (if (set-member? st v) #f
    (begin (set-add! st v) #t)))

;; turning our "streams" into Racket streams.
(define/match (s->stream s)
  [('()) empty-stream]
  [((cons x xs)) (stream-cons x (s->stream xs))]
  [((? procedure? a)) (s->stream (a))])


;; Computations form a functor, an applicative, an alternative, and a monad.
(define (c/run c st)
  (match c
    [#t (s/pure (Got (void) st))]
    [#f s/empty]
    [(? procedure?) (c st)]))

(define/match (c/pure x)
  [((? void? x)) #t]
  [(x) (lambda (st) (s/pure (Got x st)))])

(define/match (c/join x)
  [(#t) (error "cannot join #t")]
  [(#f) #f]
  [((? procedure? x))
    (lambda (st)
      (s/bind (x st)
        (lambda (r) (c/run (Got-value r) (Got-state r)))))])

(define (c/map1 f c)
  (match c
    [#t (c/pure (f (void)))]
    [#f c]
    [(? procedure?) (lambda (st) (s/map1 (curry got/map1 f) (c st)))]))

(define (c/bind x f) (c/join (c/map1 f x)))

(define/match (c/seq cs [accum '()])
  [('() accum) (c/pure (reverse accum))]
  [((cons c cs) accum)
    (c/bind c (lambda (x) (c/seq cs (cons x accum))))])

(define (c/map f . xs)
  (c/map1 (curry apply f) (c/seq xs)))

(define ((c/fresh [name #f]) st )
  (s/pure (Got (Var (State-next-id st) name)
            (struct-copy State st [next-id (+ 1 (State-next-id st))]))))

(define ok #t)
(define fail #f)

(define/match (alt x y)
  [(#t #t) #t]
  [(#f b) b]
  [(a #f) a]
  [(a b) (lambda (st) (s/alt (c/run a st) (c/run b st)))])


;; Control operators
(fn conj
  [() ok]
  [(x) x]
  [(#t . xs) (apply conj xs)]
  [(#f . _) #f]
  [(x . xs) (c/bind x (lambda (_) (apply conj xs)))])

(fn disj
  [() fail]
  [(x) x]
  [(#f . xs) (apply disj xs)]
  [(x . xs) (alt x (apply disj xs))])

(define-syntax-rule (zzz e)
  (lambda (st) (lambda () (c/run e st))))

(define-syntax fresh
  (syntax-rules ()
    [(fresh () body ...) (conj body ...)]
    [(fresh (v vs ...) body ...)
      (c/bind (c/fresh 'v) (lambda (v) (fresh (vs ...) body ...)))]))

(define-syntax condo
  (syntax-rules ()
    [(condo) fail]
    [(condo (head term ...) ...)
      (zzz (disj (conj head term ...) ...))]))

(define ((trace name term . gs) st)
  (printf "~a: ~a\n" name (walk term (State-subst st)))
  (c/run (apply conj gs) st))

(define ($! test . terms)
  ()
  )


;;; Runners
(define (run-goal-raw g [state empty-state])
  (stream-map (compose State-subst Got-state) (s->stream (c/run g state))))

(define (run-goal g [n 10] [state empty-state])
  ;; hacky open coded stream-take
  (for/list ([sub (run-goal g)]
             [_ (in-range n)])
    (for/hash ([(k v) (in-hash sub)])
      (values k (walk v sub)))))

(define-syntax solns
  (syntax-rules ()
    )
  )

(define-syntax solve
  (syntax-rules ()
    [(solve (v ...) goal) (solve (v ...) goal 10)]
    [(solve (v ...) goal n) (solve (v ...) goal n empty-state)]
    [(solve (v ...) goal n state)
      (solve-results
        (fresh (v ...) (c/map1 (lambda (_) (list v ...)) goal))
        n state)]))

(define (solve-results goal n state)
  (for/list ([got (s->stream (c/run goal state))]
             [_ (in-range n)])
    (define sub (State-subst (Got-state got)))
    (for/hash ([var (Got-value got)]
                #:when (hash-has-key? sub (Var-id var)))
      (values (or (Var-name var) (Var-id var)) (walk var sub)))))


;; Unification / equivalence
(define/match (equalo a b)              ;an optimization of equalo-slow
  ;; trivial optimisation
  [((Var a-id _) (Var b-id _)) #:when (eq? a-id b-id) ok]
  ;; if either is a var and they're not obviously equal, need to wait for
  ;; substitution
  [((and a (? Var?)) b) (equalo-slow a b)]
  [(a (and b (? Var?))) (equalo-slow a b)]
  ;; if they're conses we can deconstruct them
  [((cons ax ay) (cons bx by))
    (conj (equalo ax bx) (equalo ay by))]
  ;; either one is a cons and the other isn't (in which case they're unequal and
  ;; un-unifiable), or they're both non-conses (in which case they can't contain
  ;; variables and we can compare them directly)
  [(a b) (if (equal? a b) ok fail)])

(define ((equalo-slow a b) st)
  (define sub (State-subst st))
  (define new-sub (unify sub (walk a sub) (walk b sub)))
  (if new-sub
    (s/pure (Got (void) (struct-copy State st [subst new-sub])))
    s/empty))

(define (unify sub a b)
  (match* (a b)
    [((Var a _) (Var b _)) #:when (eq? a b) sub]
    [((? Var? a) b) (extend a b sub)]
    [(a (? Var? b)) (extend b a sub)]
    [((cons xl xr) (cons yl yr))
      (let ([sub (unify sub xl yl)])
        (and sub (unify sub xr yr)))]
    [(a b) #:when (equal? a b) sub]
    [(_ _) #f]))
