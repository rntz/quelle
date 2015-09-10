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

(define (set-apply f . args)
  (match (apply list* args)
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

(define (set-apply/set f . args)
  (match (apply list* args)
    ['() (f)]
    [(list a) (set-call/set f a)]
    [(list a b) (set-call/set f a b)]
    [(list a b c) (set-call/set f a b c)]
    [(list a b c d) (set-call/set f a b c d)]
    [(list a b c d e) (set-call/set f a b c d e)]
    [(list a b c d e f) (set-call/set f a b c d e f)]
    [(list a b c d e f g) (set-call/set f a b c d e f g)]
    [_ (let*/set ([x (cross-the-streams (map set->stream args))])
         (apply f x))]))

;; takes cartesian cross product of a list of streams
(define (cross-the-streams streams)
  (error "unimplemented"))              ;TODO
