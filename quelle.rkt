#lang racket

(require (for-syntax syntax/parse))

(define (assert! t) (unless t (error "ASSERTION FAILURE")))
(define (warn! msg) (displayln (format "WARNING: ~a" msg)) )

(define (set-unions sets) (for*/set ([s sets] [x s]) x))

(define-syntax set-call
  (syntax-parser
    [(_ f a ...)
      (with-syntax ([(x ...)
                      (map (lambda (_) (gensym)) (syntax->list #'(a ...)))])
        #'(for*/set ([x a] ...) (f x ...)))]))

(define (set-apply f args)
  (match args
    ['() (f)]
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

(define (eqmap eq l . lsts)
  (define len (length l))
  (and (andmap (lambda (l) (= len (length l))))
       (apply andmap eq l lsts)))

(define (all xs) (andmap identity xs))

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

(define (unpair l) (values (map car l) (map cdr l)))

(define (unzip n l [get list-ref])
  (values
    (for/list ([i (in-range n)])
      (map (lambda (x) (get x i)) l))))


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

;;; utility, might come in handy
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
(define (type-error! msg) (raise (type-error msg)))

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
  [(_ _) (type-error! "could not find lub")])

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


;;; Type inference/checking/synthesis/elaboration
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
          (define Γ' (check-pat Γ subj-t (car b)))
          (elab (append Γ' Γ) (cdr b))))
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

(define (lit-type l)
  (cond
    [(boolean? l) (t-bool)]
    [(number? l) (t-num)]
    [(string? l) (t-str)]
    [#t (type-error! "unknown literal type")]))


;;; Evaluation of injected expressions
(define (eval l σ e)
  (define rel (match l ['F #f] ['R #t]))
  (define (F) (assert! (eq? l 'F)))
  (define (R) (assert! (eq? l 'R)))
  (define pure (if rel set identity))
  (define apply* (if rel set-apply apply))
  (define-syntax-rule (call f a ...)
    (if rel (set-call f a ...) (f a ...)))
  (match e
    ;; TODO: wrap v in contract checking its type
    [(e-base v _) (pure v)]
    [(e-var _ i) (pure (list-ref σ i))]
    [(e-empty) (R) (set)]
    [(e-union a b) (R) (set-union (eval 'R σ a) (eval 'R σ b))]
    [(e-set e) (pure (eval 'R σ e))]
    [(e-any e) (R) (set-unions (eval 'R σ e))]
    [(e-tuple es)
      (apply* vector-immutable (map (lambda (x) (eval l σ x)) es))]
    [(e-proj i e) (call (lambda (x) (vector-ref i x)) (eval l σ e))]
    [(e-tag tag e) (call (lambda (x) (list tag e))) (eval l σ e)]
    [(e-app f a)
      ;; FIXME: wrong
      ;; need to know whether we're applying a fun or rel!
      ;; behavior also varies by level.
      (call (lambda (f x) (f x)) (eval l σ f) (eval l σ a))]
    [(e-fun v vtype body)
      (error "unimplemented")]
    [(e-rel v vtype body) (error "unimplemented")]
    [(e-case subj branches) (error "unimplemented")]
    ))

;; (define (eval σ e)
;;   (match e
;;     ;; TODO: wrap v in contract checking its type
;;     [(e-base v _) v]
;;     [(e-var _ i) (list-ref σ i)]
;;     [(e-empty) (set)]
;;     [(e-union l r) (set-union (eval σ l) (eval σ r))]
;;     [(e-set e) (eval σ e)] ;; is this right?
;;     [(e-any e) (eval σ e)] ;; is this right?
;;     ;; THIS IS WRONG.
;;     ;; what if we're in relational context?
;;     [(e-tuple es) (apply vector-immutable (map (lambda (x) (eval σ x)) es))]
;;     [(e-proj i e) (vector-nth i )]
;;     ))

;; ;;; run
;; (define (run l σ e)
;;   (define ret (match l ['F identity] ['R set]))
;;   (match e
;;     [(e-base v _) (ret v)]
;;     [(e-var _ idx) (ret (list-ref σ i))]
;;     ))


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
