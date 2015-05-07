#lang racket

(provide define-syntax-parser fn flip)

(require racket (for-syntax syntax/parse))
(define-syntax define-syntax-parser
  (syntax-parser
    [(_ name:id (pattern body ...) ...)
      #'(define-syntax name
          (syntax-parser
            (pattern body ...)
            ...))]
    [(_ (name:id pattern ...) body ...)
      #'(define-syntax-parser name
          [(_ pattern ...) body ...])]))

(begin-for-syntax
  (define-syntax-class fn-clause
    (pattern ((param ...) body ...)
      #:attr pattern #'(list param ...))
    (pattern ((param ... . rest-param:id) body ...)
      #:attr pattern #'(list-rest param ... rest-param))))

(define-syntax-parser fn
  [(_ (name params ...) body ...)
    #'(define (name params ...) body ...)]
  [(_ name:id c:fn-clause ...)
    #'(define/match (name . _)
        [(c.pattern) c.body ...]
        ...)])


;; Combinators
(define ((flip f) x y) (f y x))
