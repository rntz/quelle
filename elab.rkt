#lang racket

(require "util.rkt" "ast.rkt" "types.rkt")
(provide (all-defined-out))

;;; Type inference / expression elaboration
;;; TODO: where do env-* belong?
(define env-cons cons)
(define env-ref list-ref)
(define (env-extend extension env) (append (reverse extension) env))

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
      (define level (level-max* (map car exps)))
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
      (values (t-sum (hash tag t)) (cons (car e) (e-tag tag e)))]

    [(e-case subj branches)
      (define-values (subj-t subj-e) (elab Γ subj))
      (define-values (branch-ts branch-es)
        (for/lists (types levels) ([b branches])
          (define Γ- (check-pat Γ subj-t (car b)))
          (elab (append Γ- Γ) (cdr b))))
      (values (types-lub branch-ts)
        (cons (level-max* (car subj-e) (map car branch-es))
          (e-case subj-e (map cons (map car branches) branch-es))))]

    [(e-app func args)
      (define-values (ftype fexp) (elab Γ func))
      (define-values (atypes aexps)
        (for/lists (ts es) ([a args]) (elab Γ a)))
      (define-values (argtypes outtype app level)
        (match ftype
          [(t-fun as b)
            (values as b e-app-fun (level-max* (car fexp) (map car aexps)))]
          [(t-rel as b) (values as b e-app-rel 'R)]
          [(t-bot)
            (assert! (R? (car fexp)))
            (warn! "applying empty set")
            (values #f (t-bot) e-app-rel 'R)]
          [_ (type-error! "can only apply functions or relations")]))
      (when (and argtypes (not (subtypes? atypes argtypes)))
        ;; TODO: better error message here
        (type-error! "wrong argument type(s)"))
      (values outtype (cons level (app fexp aexps)))]

    [(e-fun args atypes body)
      (define-values (body-type body-exp) (elab (env-extend atypes Γ) body))
      (unless (F? (car body-exp))
        (type-error! "function bodies must be functional"))
      (values (t-fun atypes body-type) (F (e-fun args atypes body-exp)))]

    [(e-rel args atypes body)
      (define-values (body-type body-exp) (elab (env-extend atypes Γ) body))
      (values (t-rel atypes body-type) (F (e-rel args atypes body-exp)))]))

(define (check-pat Γ t p)
  (match p
    [(p-wild) '()]
    [(p-var _) (list t)]
    [(p-lit l)
      (if (subtype? t (or (lit-type l) (type-error! "unknown literal type")))
        '()
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
