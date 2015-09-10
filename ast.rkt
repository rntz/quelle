#lang racket

(require "util.rkt")
(provide (all-defined-out))

;; AST types
(define (F? x) (eq? x 'F))
(define (R? x) (eq? x 'R))
(define (level? x) (or (F? x) (R? x)))
(define/contract (level-max l r)
  (-> level? level? level?)
  (if (or (R? l) (R? r)) 'R 'F))
(define (level-max* . args)
  (foldl level-max 'F (apply list* args)))

(enum type
  (t-bool) (t-num) (t-str)
  ;; branches is a hash mapping names to types
  (t-sum branches)
  (t-tuple types)
  (t-fun args result) (t-rel args result)
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
  (e-app func args)
  (e-fun vars types body) (e-rel vars types body))

(enum pat
  (p-wild)
  (p-var name)
  (p-tuple pats)
  (p-tag tag pat)
  (p-lit lit))

;;; Utilities
(define (lit? x) (if (lit-type x) #t #f))
(define (lit-type l)
  (cond
    [(boolean? l) (t-bool)]
    [(number? l) (t-num)]
    [(string? l) (t-str)]
    [#t #f]))
