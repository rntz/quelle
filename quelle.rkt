#lang racket

(define (set-unions sets) (foldl set-union (set) sets))

;;; PROBLEM: Kleisli(FinSet) isn't monoidal closed.
;;; There's probably an extension of it that is, though.

;; FEM = Finitely expansive maps.
;; category of sets with f : A -> B being a a function f : A -> FinSet(B).
;; symmetric monoidal under x, 1.
;; semiadditive: cartesian & cocartesian and products & coproducts coincide.
;; monoidal closed???
;;
;; [A -o B] = [A] -> FinSet [B]
;; I think this works. Have details in notebook.

;; Need exponentials!
;;
;;
;; ----------------
;; Δ,x:A; Γ ⊢ x : A
;;
;;   Δ;· ⊢ e : A
;; ----------------
;; Δ;· ⊢ box e : !A
;;
;; Δ;Γ₁ ⊢ e₁ : !A  Δ,x:A; Γ₂ ⊢ e₂ : B
;; ----------------------------------
;; Δ;Γ₁,Γ₂ ⊢ let box x = e₁ in e₂ : B
;;
;; What's the meaning of these in Rel? In FEM?
;;
;; In Rel, ! is the powerset functor. [!A] = FinSet([A])
;;
;;      [Δ;Γ ⊢ e : A] ∈ FinSet([Δ]) × [Γ] → FinSet([A]) ??
;;
;;      [Δ;· ⊢ box e : !A] ∈ FinSet([Δ]) × 1 → FinSet(FinSet([A]))
;;      [box e] =? λ δ,⟨⟩. {[e](δ,⟨⟩)}              -- seems likely
;;      [box e] =? λ δ,⟨⟩. FinSet([e](δ,⟨⟩))        -- likely? plausible?
;;      [box e] =? λ δ,⟨⟩. {{x} | x ∈ [e](δ,⟨⟩)}    -- probably not
;;
;; shouldn't LPC paper explain how to derive this from the adjoint functors?
;;
;; In FEM, is ! the finite powerset functor?

;; Language of relations:
;;
;; decls    d ::= x := e
;;                x e := p = e, ...     -- sugar for (x := {e | p <- e, ...})
;;
;; exprs    e ::= empty | e union e
;;                C(e, ...)
;;                case e of p -> e; ...
;;                app E(e, ...)
;;                pure E
;;                x
;;
;; racket exprs: E
;;
;; patterns p ::= x | (p, ...) | C(p...) | _
;;                L
;;
;; vars     x
;;
;; racket literals          L
;; symbols (constructors)   C

;; How do I interpret recursion?
;; - Don't need it for now.

;; Sugars:
;;      (let p = e1 in e2)      => (case e1 of p -> e2)
;;      {e | p1 = e1, ... }     => (let p1 = e1 in ... e)
;;        (can also just use bare "e", which means "_ = e")
;;      when E                  => (let #t = expr E in ())
;;      (e, ...)                => list(e, ...)
;;
;;      -- an unordered `case' statement; matches all branches in parallel
;;      (union case e           => let x = e in
;;          of p1 -> e1;             (let p1 = x in e1)
;;             ...                   union ...
;;             pn -> en)             union (let pn = x in en)

(struct expr () #:transparent)
(struct e-var expr (name) #:transparent)
(struct e-empty expr () #:transparent)
(struct e-union expr (left right) #:transparent)
(struct e-pure expr (value) #:transparent)
(struct e-app expr (func args) #:transparent)
;; branches is a list of (pat . expr) pairs.
(struct e-case expr (subject branches) #:transparent)

(define (compile e [ctx '()])
  (define (recur x) (compile x ctx))
  (match e
    ;; shouldn't this depend on context?
    [(e-var name) name]
    [(e-empty) #'(set)]
    [(e-union l r) #`(set-union #,(compile l ctx) #,(compile r ctx))]
    [(e-pure e) #`(set #,e)]
    [(e-app f args)
      (unless (procedure? f) (error "applying non-procedure"))
      (with-syntax ([(e ...) (map recur args)]
                    [(x ...) (map (lambda (_) (gensym)) args)])
        #`(for*/set ([x e] ...)
            (#,f x ...)))]
    [(e-case subject branches)
      ;; FIXME: need to compile e in a different context!
      (define/match (fixup x)
        [((cons p e)) (cons p (recur e))])
      (with-syntax ([((p . e) ...) (map fixup branches)])
        #`(set-unions
            (for*/list ([x #,(compile subject ctx)])
              (match x
                [p e] ...
                [_ (set)]))))]))
