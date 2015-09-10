#lang racket

(require "util.rkt" "ast.rkt" "types.rkt" "elab.rkt" "sets.rkt")
(provide (all-defined-out))

;;; Evaluation of elaborated expressions
(define make-tuple vector)
(define tuple-ref vector-ref)
(define (make-tag tag exp) (list tag exp))

(define (eval-R σ level-expr)
  (define (recur x) (eval-R σ x))
  (match-define (cons level expr) level-expr)
  (if (F? level)
    (set (eval-F σ level-expr))
    (match expr
      [(e-empty) (set)]
      [(e-union a b) (set-union (recur a) (recur b))]
      [(e-any e)
        (match (car e)
          ['F (eval-F σ e)]
          ['R (set-unions (recur e))])]
      [(e-tuple es)
        (set-apply make-tuple (map recur es))]
      [(e-proj i e) (for/set ([v (recur e)]) (tuple-ref v i))]
      [(e-tag tag e) (for/set ([v (recur e)]) (make-tag tag v))]
      [(e-case subj branches)
        (let*/set ([sv (recur subj)])
          (let loop ([bs branches])
            (match bs
              ['() (error "no case matched")]
              [(cons (cons p e) bs)
                (match (pat-match p sv)
                  [#f (loop bs)]
                  [σ- (eval-R (append σ- σ) e)])])))]
      [(e-app-fun func args)
        (match (car func)
          ['F (set-apply (eval-F σ func) (map recur args))]
          ['R (set-apply apply (recur func) (map recur args))])]
      [(e-app-rel func args)
        (match (car func)
          ['F (set-apply/set (eval-F σ func) (map recur args))]
          ['R (set-apply/set apply (recur func) (map recur args))])]
      [_ (error "internal error: not an R expression")])))

(define (eval-F σ level-expr)
  (define (recur x) (eval-F σ x))
  (match-define (cons level expr) level-expr)
  (unless (F? level) (error "internal error: got R, expected F"))
  (match expr
    [(e-base v _) v]
    [(e-var _ i) (env-ref σ i)]
    [(e-set e) (eval-R σ e)]
    [(e-tuple es) (apply make-tuple (map recur es))]
    [(e-proj i e) (tuple-ref (recur e) i)]
    [(e-tag tag e) (make-tag tag (recur e))]
    [(e-case subj branches)
      (define sv (recur subj))
      (let loop ([bs branches])
        (match bs
          ['() (error "no case matched")]
          [(cons (cons p e) bs)
            (match (pat-match p sv)
              [#f (loop bs)]
              [σ- (eval-F (append σ- σ) e)])]))]
    [(e-app-fun fnc arg) (apply (recur fnc) (map recur arg))]
    [(e-fun _ _ body) (lambda as (eval-F (env-extend as σ) body))]
    [(e-rel _ _ body) (lambda as (eval-R (env-extend as σ) body))]
    [_ (error "internal error: not an F expression")]))

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
