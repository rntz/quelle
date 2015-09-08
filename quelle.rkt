#lang racket

;; FEM = Finitely expansive maps.
;; category of sets with f : A -> B being a a function f : A -> FinSet(B).
;; symmetric monoidal under x, 1.
;; semiadditive: cartesian & cocartesian and products & coproducts coincide.
;;
;; [A -o B] = [A] -> FinSet [B]
;;
;; Does *not* AFAIK form a model of linear logic *with exponentials*. That is to
;; say, there's no model for the ! connective. There's an adjunction with Set,
;; but it's not a monoidal adjunction (doesn't preserve the monoidal structure
;; used by contexts).

;; "Adjoint" language of FEMs.
;; NB. two *different* kinds of functions!
;; (A -> B): regular functions, 1-output (if terminating)
;; (A => B): finitely expansive maps, finitely-many-outputs.
;;
;; types    A ::= A x A
;;
;; exprs    e ::= empty | e union e | set e | any e
;;                x | fun x -> e | rel x -> e | e e
;;                (e,...) | πᵢ e
;;                case e of p -> e; ...
;;                C | L | P
;;
;; literals L = booleans, numbers, strings
;; ctors    C = symbols
;; prims    P = + | - | * | / | == | <= | print
;;
;; patterns p ::= x | _ | (p, ...) | C p | L
;;
;; vars     x
;;

;; How do I interpret recursion?
;; - Don't need it for now.

;; Sugars:
;;      (let p = e1 in e2)      => (case e1 of p -> e2)
;;      {e | p1 = e1, ... }     => (let p1 = e1 in ... in e)
;;        (can also just use bare "ei", which means "_ = ei")
;;      when e                  => (let #t = e in ())
;;
;;      -- an unordered `case' statement; matches all branches in parallel
;;      (union case e           => let x = e in
;;          of p1 -> e1;             (let p1 = x in e1)
;;             ...                   union ...
;;             pn -> en)             union (let pn = x in en)

(require (for-syntax syntax/parse))


;;; Miscellaneous utilities
(define (assert! t) (unless t (error "ASSERTION FAILURE")))
(define (warn! msg) (displayln (format "WARNING: ~a" msg)) )

(define-syntax-rule (let*/set ((p e) ...) body)
  (for*/set ([p e] ... [x body]) x))

(define (set-unions sets) (let*/set ([s sets]) s))

(define-syntax set-call
  (syntax-parser
    [(_ f a ...)
      (with-syntax ([(x ...)
                      (map (lambda (_) (gensym)) (syntax->list #'(a ...)))])
        #'(for*/set ([x a] ...) (f x ...)))]))

(define (set-apply f args)
  (match args
    ['() (set (f))]
    [(list a) (set-call f a)]
    [(list a b) (set-call f a b)]
    [(list a b c) (set-call f a b c)]
    [(list a b c d) (set-call f a b c d)]
    [(list a b c d e) (set-call f a b c d e)]
    [(list a b c d e f) (set-call f a b c d e f)]
    [(list a b c d e f g) (set-call f a b c d e f g)]
    ;; is it really better to use streams here than to use lists or sets or
    ;; vectors?
    [_ (for/set ([x (cross-the-streams (map set->stream args))])
         (apply f x))]))

;; takes cartesian cross product of a list of streams
(define (cross-the-streams streams)
  (error "unimplemented"))              ;TODO

(define (index-of v lst)
  (let loop ([i 0] [l lst])
    (match l
      ['() #f]
      [(cons x xs) (if (equal? x v) i (loop (+ 1 i) xs))])))

(define (eqmap eq l . lsts)
  (define len (length l))
  (and (andmap (lambda (l) (= len (length l))))
       (apply andmap eq l lsts)))

(define (dict-union-with a b f)
  (define keys (set-union (list->set (dict-keys a)) (list->set (dict-keys b))))
  (for/hash ([k keys])
    (if (not (dict-has-key? a k))
      (dict-ref b k)
      (if (not (dict-has-key? b k))
        (dict-ref a k)
        (f (dict-ref a k) (dict-ref b k))))))

(define (dict-intersection-with a b f)
  (for/hash ([k (in-dict-keys a)]
              #:when (dict-has-key? b k))
    (f (dict-ref a k) (dict-ref b k))))

(define-syntax-rule (enum-case enum-name (branch-name args ...))
  (struct branch-name enum-name (args ...) #:transparent))

(define-syntax-rule (enum name branch ...)
  (begin
    (struct name () #:transparent)
    (enum-case name branch) ...))


;; AST types
(define (F? x) (eq? x 'F))
(define (R? x) (eq? x 'R))
(define (level? x) (or (F? x) (R? x)))
(define/contract (level-max l r)
  (-> level? level? level?)
  (if (or (R? l) (R? r)) 'R 'F))

(define (level-maximum l) (foldl level-max 'F l))

(enum type
  (t-bool) (t-num) (t-str)
  ;; branches is a hash mapping names to types
  (t-sum branches)
  (t-tuple types)
  ;; TODO?: enforce invariant that dom is never (t-bot)?
  (t-fun dom cod) (t-rel dom cod)
  (t-set type)
  (t-bot))

(enum expr
  ;; used for literals & primitive functions.
  (e-base value type)
  (e-var name index) ;; DeBruijn indexing
  (e-empty) (e-union left right)
  (e-set expr) (e-any expr)
  (e-tuple exprs) (e-proj index expr)
  (e-tag tag expr)
  ;; branches is a list of (pat . expr) pairs. TODO: use a struct!
  (e-case subject branches)
  (e-app func arg)
  (e-fun var type body) (e-rel var type body))

(enum pat
  (p-wild)
  (p-var name)
  (p-tuple pats)
  (p-tag tag pat)
  (p-lit lit))

;;; Utilities
(define (lit? x)
  (or (boolean? x) (number? x) (string? x)))

(define (lit-type l)
  (cond
    [(boolean? l) (t-bool)]
    [(number? l) (t-num)]
    [(string? l) (t-str)]
    [#t (type-error! "unknown literal type")]))

(define (map-subexprs f e)
  (match e
    [(or (e-var _ _) (e-empty) (e-base _ _)) e]
    [(e-set e) (e-set (f e))]
    [(e-any e) (e-any (f e))]
    [(e-fun var type body) (e-fun var type (f body))]
    [(e-rel var type body) (e-rel var type (f body))]
    [(e-app fnc arg) (e-app (f fnc) (f arg))]
    [(e-tuple es) (e-tuple (map f es))]
    [(e-tag tag expr) (e-tag tag (f expr))]
    [(e-proj index expr) (e-proj index (f expr))]
    [(e-case subj branches)
      (e-case (f subj)
        (map (lambda (x) (cons (car x) (f (cdr x)))) branches))]))


;; Type manipulation
(struct type-error exn:fail:user () #:transparent)
(define (type-error! msg) (raise (type-error msg (current-continuation-marks))))

(define/match (subtype? a b)
  [((t-sum a) (t-sum b))
    (for/and ([(name type) (in-dict a)])
      (and (dict-has-key? b name)
           (subtype? type (dict-ref b name))))]
  [((t-set a) (t-set b)) (subtype? a b)]
  [((t-tuple a) (t-tuple b)) (eqmap subtype? a b)]
  [((t-fun ax ay) (t-fun bx by)) (and (subtype? bx ax) (subtype? ay by))]
  [((t-rel ax ay) (t-rel bx by)) (and (subtype? bx ax) (subtype? ay by))]
  [((t-bot) _) #t]
  [(a b) (equal? a b)])

;;; least upper bound of two types. errors if types have no lub.
(define/match (type-lub l r)
  [((t-bot) x) x]
  [(x (t-bot)) x]
  [((t-set a) (t-set b)) (t-set (type-lub a b))]
  [((t-fun ax ay) (t-fun bx by)) (t-fun (type-glb ax bx) (type-lub ay by))]
  [((t-rel ax ay) (t-rel bx by)) (t-rel (type-glb ax bx) (type-lub ay by))]
  [((t-tuple a) (t-tuple b))
    (if (= (length a) (length b)) (t-tuple (map type-lub a b))
      (type-error! "tuple length mismatch"))]
  [((t-sum a) (t-sum b)) (dict-union-with a b type-lub)]
  [(a b) (cond
           [(subtype? a b) b]
           [(subtype? b a) a]
           [#t (type-error! (format "could not unify ~v and ~v" a b))])])

;;; greatest lower bound of two types. always exists b/c of (t-bot)
(define (type-glb l r)
  (with-handlers ([type-error? (lambda (e) (t-bot))])
    (match* (l r)
      [((t-set a) (t-set b)) (t-set (type-glb a b))]
      [((t-fun ax ay) (t-fun bx by)) (t-fun (type-lub ax bx) (type-glb ay by))]
      [((t-rel ax ay) (t-rel bx by)) (t-rel (type-lub ax bx) (type-glb ay by))]
      [((t-tuple a) (t-tuple b)) (if (not (= (length a) (length b))) (t-bot)
                                   (t-tuple (map type-glb a b)))]
      [((t-sum a) (t-sum b)) (dict-intersection-with a b type-glb)]
      [(a b) (cond
               [(subtype? a b) a]
               [(subtype? b a) b]
               [#t (t-bot)])])))

(define (type-lub* l) (foldl type-lub (t-bot) l))


;;; Type inference / expression elaboration
(define env-cons cons)
(define env-ref list-ref)

;; Elaborated expression forms:
;; e-app-{fun,rel} distinguish between applying a function or a relation
(struct e-app-fun e-app () #:transparent)
(struct e-app-rel e-app () #:transparent)

;; Returns two values: the type, and a (level . expr) pair. In `expr', every
;; subexpr is likewise tagged with its level as a (level . expr) pair,
;; recursively. Also, e-app has been elaborated into either e-app-{fun,rel} as
;; appropriate.
(define (elab Γ e)
  (define (F x) (cons 'F x))
  (define (R x) (cons 'R x))
  (match e
    [(e-var _ i) (values (env-ref Γ i) (F e))]
    [(e-base _ t) (values t (F e))]
    [(e-empty) (values (t-bot) (R e))]
    [(e-union l r) (let*-values ([(lt le) (elab Γ l)]
                                 [(rt re) (elab Γ r)])
                     (values (type-lub lt rt) (R (e-union le re))))]
    [(e-set e-in)
      (define-values (t e) (elab Γ e-in))
      (values (t-set t) (F (e-set e)))]
    [(e-any e-in)
      (define-values (t e) (elab Γ e-in))
      (match t
        [(t-set a) (values a (R (e-any e)))]
        [(t-bot)
          (warn! "`any' applied to empty set")
          (values (t-bot) (R (e-any e)))]
        [_ (type-error! "`any' applied to non-set")])]
    [(e-tuple es)
      (define-values (types exps)
        (for/lists (types exps) ([e es]) (elab Γ e)))
      (define level (level-maximum (map car exps)))
      (values (t-tuple types) (cons level (e-tuple exps)))]
    [(e-proj index e-in)
      (define-values (t e) (elab Γ e-in))
      (match t
        [(t-tuple ts)
          (if (< index (length ts))
            (values (list-ref ts index) (cons (car e) (e-proj index e)))
            (type-error! "tuple too short"))]
        [(t-bot)
          (assert! (R? (car e)))
          (warn! "projecting from empty set")
          (values (t-bot) (R (e-proj index e)))]
        [_ (type-error! "projecting from non-tuple")])]
    [(e-tag tag e-in)
      (define-values (t e) (elab Γ e-in))
      (values (t-sum (hash tag t)) (cons (car e) (e-tag e)))]
    [(e-case subj branches)
      (define-values (subj-t subj-e) (elab Γ subj))
      (define-values (branch-ts branch-es)
        (for/lists (types levels) ([b branches])
          (define Γ- (check-pat Γ subj-t (car b)))
          (elab (append Γ- Γ) (cdr b))))
      (values (type-lub* branch-ts)
        (cons (level-maximum (cons (car subj-e) (map car branch-es)))
          (e-case subj-e (map cons (map car branches) branch-es))))]
    [(e-app fnc arg)
      (define-values (ftype fexp) (elab Γ fnc))
      (define-values (atype aexp) (elab Γ arg))
      (match ftype
        [(t-fun a b)
          (define level (level-max (car fexp) (car aexp)))
          (values b (cons level (e-app-fun fexp aexp)))]
        [(t-rel a b)
          (values b (R (e-app-rel fexp aexp)))]
        [(t-bot)
          (assert! (R? (car fexp)))
          (warn! "applying empty set")
          (values (t-bot) (R (e-app-rel fexp aexp)))]
        [_ (type-error! "can only apply functions or relations")])]
    [(e-fun v vtype body)
      (define-values (body-type body-exp) (elab (env-cons vtype Γ) body))
      (unless (F? (car body-exp))
        (type-error! "function bodies must be functional"))
      (values (t-fun vtype body-type) (F (e-fun v vtype body-exp)))]
    [(e-rel v vtype body)
      (define-values (body-type body-exp) (elab (env-cons vtype Γ) body))
      (values (t-rel vtype body-type) (F (e-rel v vtype body-exp)))]))

(define (check-pat Γ t p)
  (match p
    [(p-wild) '()]
    [(p-var _) (list t)]
    [(p-lit l)
      (if (subtype? t (lit-type l)) '()
        (type-error! "wrong type when matched against literal"))]
    [(p-tuple pats)
      ((compose append* reverse)
        (match t
          [(t-bot) (map (lambda (x) (check-pat Γ (t-bot) x)) pats)]
          [(t-tuple types)
            (if (= (length types) (length pats))
              (map (lambda (t p) (check-pat Γ t p)) types pats)
              (type-error! "wrong length tuple pattern"))]
          [_ (type-error! "not a tuple")]))]
    [(p-tag tag pat)
      (match t
        [(t-sum bs) (if (dict-has-key? bs tag)
                      (check-pat Γ (dict-ref bs tag) pat)
                      ;; FIXME: this is actually ok, it's just dead code; it
                      ;; should warn, not error.
                      (type-error! "no such branch in tagged some"))]
        [(t-bot) (check-pat Γ (t-bot) pat)]
        [_ (type-error! "not a sum")])]))


;;; Evaluation of elaborated expressions
(define make-tuple vector)
(define tuple-ref vector-ref)
(define (make-tag tag exp) (list tag exp))

(define (eval-R σ level-expr)
  (match-define (cons level expr) level-expr)
  (if (F? level)
    (set (eval-F σ level-expr))
    (match expr
      [(e-empty) (set)]
      [(e-union a b) (set-union (eval-R σ a) (eval-R σ b))]
      [(e-any e)
        (match (car e)
          ['F (eval-F σ e)]
          ['R (set-unions (eval-R σ e))])]
      [(e-tuple es)
        (set-apply make-tuple (map (lambda (e) (eval-R σ e)) es))]
      [(e-proj i e) (for/set ([v (eval-R σ e)]) (tuple-ref v i))]
      [(e-tag tag e) (for/set ([v (eval-R σ e)]) (make-tag tag v))]
      [(e-case subj branches)
        (let*/set ([sv (eval-R subj)])
          (let loop ([bs branches])
            (match bs
              ['() (error "no case matched")]
              [(cons (cons p e) bs)
                (match (pat-match p sv)
                  [#f (loop bs)]
                  [σ- (eval-R (append σ- σ) e)])])))]
      [(e-app-fun fnc arg)
        (match (car fnc)
          ['F (let ((fv (eval-F σ fnc)))
                (for/set ([av (eval-R σ arg)]) (fv av)))]
          ['R (for*/set ([fv (eval-R σ fnc)] [av (eval-R σ arg)])
                (fv av))])]
      [(e-app-rel fnc arg)
        (match (car fnc)
          ['F (let ([fv (eval-F σ fnc)])
                (let*/set ([av (eval-R σ arg)])
                  (fv av)))]
          ['R (let*/set ([fv (eval-R σ fnc)] [av (eval-R σ arg)])
                 (fv av))])]
      [_ (error "internal invariant violation: not an R expression")])))

(define (eval-F σ level-expr)
  (match-define (cons level expr) level-expr)
  (unless (F? level) (error "internal invariant violation: got R, expected F"))
  (match expr
    [(e-base v _) v]
    [(e-var _ i) (env-ref σ i)]
    [(e-set e) (eval-R σ e)]
    [(e-tuple es) (apply make-tuple (map (lambda (e) (eval-F σ e)) es))]
    [(e-tag tag e) (make-tag tag (eval-F σ e))]
    [(e-case subj branches)
      (define sv (eval-F σ subj))
      (let loop ([bs branches])
        (match bs
          ['() (error "no case matched")]
          [(cons (cons p e) bs)
            (match (pat-match p sv)
              [#f (loop bs)]
              [σ- (eval-F (append σ- σ) e)])]))]
    [(e-app-fun fnc arg) ((eval-F σ fnc) (eval-F σ arg))]
    [(e-fun _ _ body) (lambda (x) (eval-F (env-cons x σ) body))]
    [(e-rel _ _ body) (lambda (x) (eval-R (env-cons x σ) body))]
    [_ (error "internal invariant violation: not an F expression")]))

;; returns either #f for no match or an env to be added to the current one
(define/match (pat-match pat val)
  [((p-wild) _) '()]
  [((p-var _) v) (list v)]
  [((p-tuple ps) (? vector? vs))
    (let loop ([ps ps] [vs (vector->list vs)] [σ '()])
      (match* (ps vs)
        [('() '()) σ]
        [((cons p ps) (cons v vs))
          (define σ- (pat-match p v))
          (and σ- (loop ps vs (append σ- σ)))]))]
  [((p-tag tag p) (list vtag v)) (and (equal? tag vtag) (pat-match p v))]
  [((p-lit l) v) (and (equal? l v) '())])


;;; Parsing s-expressions as exprs.
(define (parse e [env '()])
  (match e
    [(? lit? x) (e-base x (lit-type x))]
    ['empty (e-empty)]
    [`(union ,a ,b) (e-union (parse a env) (parse b env))]
    [`(set ,a) (e-set (parse a env))]
    [`(any ,a) (e-any (parse a env))]
    [`(list . ,es) (e-tuple (map (lambda (x) (parse x env)) es))]
    [`(get ,(? number? index) ,a) (e-proj index (parse a env))]
    [(or `(tag ,(? symbol? name) ,a)
         `((,'quote ,(? symbol? name)) ,a))
      (e-tag name (parse a env))]
    [`(case ,subj . ,branches)
      (e-case (parse subj env)
        (for/list ([b branches])
          (match-define `(,p ,e) b)
          (define pat (parse-pat p env))
          (define value (parse e (append (pat-env pat) env)))
          (cons pat value)))]
    [`(fn (,x ,t) ,body)
      (e-fun x (parse-type t) (parse body (cons x env)))]
    [`(rel (,x ,t) ,body)
      (e-rel x (parse-type t) (parse body (cons x env)))]
    [(or `(app ,f ,a) `(,f ,a)) (e-app (parse f env) (parse a env))]
    [(or `(var ,name) (? symbol? name))
      (define index (index-of name env))
      (if index (e-var name index)
        (error (format "unbound variable: ~a" name)))]))

(define (parse-type type)
  (match type
    ['bool (t-bool)] ['num (t-num)] ['str (t-str)]
    [`(set ,t) (t-set (parse-type t))]
    ['bot (t-bot)]
    [`(tuple . ,ts) (t-tuple (map parse-type ts))]
    [`(sum . ,bs)
      (t-sum (for/hash ([b bs])
               (match-define `(,name ,type) b)
               (values name (parse-type type))))]
    [`(-> ,x ,y) (t-fun (parse-type x) (parse-type y))]
    [`(=> ,x ,y) (t-rel (parse-type x) (parse-type y))]))

(define (parse-pat pat env)
  (match pat
    ['_ (p-wild)]
    [(? lit? l) (p-lit l)]
    [(or `(tag ,tag-name ,p)`(',(? symbol? tag-name) ,p))
      (p-tag tag-name (parse-pat p env))]
    [(? symbol? name) (p-var name)]
    [(or `(list . ,ps) (? list? ps))
      (p-tuple (map (lambda (x) (parse-pat x env)) ps))]))

(define (pat-env pat)
  (match pat
    [(or (p-wild) (p-lit _)) '()]
    [(p-var name) (list name)]
    [(p-tuple ps) (append* (reverse (map pat-env ps)))]
    [(p-tag _ p) (pat-env p)]))


;; (define (compile e [ctx '()])
;;   (define (recur x) (compile x ctx))
;;   (match e
;;     ;; shouldn't this depend on context?
;;     [(e-var name) name]
;;     [(e-empty) #'(set)]
;;     [(e-union l r) #`(set-union #,(compile l ctx) #,(compile r ctx))]
;;     [(e-pure e) #`(set #,e)]
;;     [(e-app f args)
;;       (unless (procedure? f) (error "applying non-procedure"))
;;       (with-syntax ([(e ...) (map recur args)]
;;                     [(x ...) (map (lambda (_) (gensym)) args)])
;;         #`(for*/set ([x e] ...)
;;             (#,f x ...)))]
;;     [(e-case subject branches)
;;       ;; FIXME: need to compile e in a different context!
;;       (define/match (fixup x)
;;         [((cons p e)) (cons p (recur e))])
;;       (with-syntax ([((p . e) ...) (map fixup branches)])
;;         #`(set-unions
;;             (for*/list ([x #,(compile subject ctx)])
;;               (match x
;;                 [p e] ...
;;                 [_ (set)]))))]))


;;; Putting it all together
(define (run expr)
  (printf "expr: ~v\n" expr)
  (define-values (type elab-expr) (elab '() expr))
  (printf "elab: ~v\n" elab-expr)
  (printf "type: ~v\n" type)
  (define val
    (match (car elab-expr)
      ['F (eval-F '() elab-expr)]
      ['R (eval-R '() elab-expr)]))
  (printf "val:  ~v\n" val))

(define (e-lit v) (e-base v (lit-type v)))
