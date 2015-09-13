#lang racket

(require "util.rkt")
(provide (all-defined-out))

;;; Set utilities
(define-syntax-rule (let*/set ((p e) ...) body)
  (for*/set ([p e] ... [x body]) x))

(define (set-unions sets) (let*/set ([s sets]) s))

;;; TODO: fix this ugly code duplication.
(define-syntax set-call/set
  (syntax-parser
    [(_ f a ...)
      (with-syntax ([(x ...)
                      (map (lambda (_) (gensym)) (syntax->list #'(a ...)))])
        #'(let*/set ([x a] ...) (f x ...)))]))

(define-syntax set-call
  (syntax-parser
    [(_ f a ...)
      (with-syntax ([(x ...)
                      (map (lambda (_) (gensym)) (syntax->list #'(a ...)))])
        #'(for*/set ([x a] ...) (f x ...)))]))

(define (set-apply func . args)
  (match (apply list* args)
    ['() (set (func))]
    [(list a) (set-call func a)]
    [(list a b) (set-call func a b)]
    [(list a b c) (set-call func a b c)]
    [(list a b c d) (set-call func a b c d)]
    [(list a b c d e) (set-call func a b c d e)]
    [(list a b c d e f) (set-call func a b c d e f)]
    [(list a b c d e f g) (set-call func a b c d e f g)]
    [(list-rest a b c d e f g etc)
      (displayln "HERE")
      (for*/set ([xa a] [xb b] [xc c] [xd d] [xe e] [xf f] [xg g]
                 [xetc (set-apply list etc)])
        (displayln "HERE")
        (apply func xa xb xc xd xe xf xg xetc))]))

(define (set-apply/set func . args)
  (match (apply list* args)
    ['() (func)]
    [(list a) (set-call/set func a)]
    [(list a b) (set-call/set func a b)]
    [(list a b c) (set-call/set func a b c)]
    [(list a b c d) (set-call/set func a b c d)]
    [(list a b c d e) (set-call/set func a b c d e)]
    [(list a b c d e f) (set-call/set func a b c d e f)]
    [(list a b c d e f g) (set-call/set func a b c d e f g)]
    [(list-rest a b c d e f g etc)
      (let*/set ([xa a] [xb b] [xc c] [xd d] [xe e] [xf f] [xg g]
                 [xetc (set-apply list etc)])
        (apply func xa xb xc xd xe xf xg xetc))]))
