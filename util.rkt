#lang racket

(require racket (for-syntax syntax/parse))

(provide
  define-syntax-parser TODO fn enum enum-case
  (for-syntax syntax-parse syntax-parser)  ;; re-export
  assert! warn! flip print-error index-of eqmap stream-take
  freeze-hash hash-union-with hash-intersection-with)

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

(define-syntax-parser TODO
  [_:id #'(error "TODO: unimplemented")])

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

(define-syntax-rule (enum-case enum-name (branch-name args ...))
  (struct branch-name enum-name (args ...) #:transparent))

(define-syntax-rule (enum name branch ...)
  (begin
    (struct name () #:transparent)
    (enum-case name branch) ...))


;;; Miscellaneous utilities
(define (assert! t) (unless t (error "ASSERTION FAILURE")))
(define (warn! msg) (displayln (format "WARNING: ~a" msg)) )

(define ((flip f) x y) (f y x))         ;do we need this?

(define (print-error err)
  (printf "error: ~a\n" (exn-message err)))

(define (index-of v lst)
  (let loop ([i 0] [l lst])
    (match l
      ['() #f]
      [(cons x xs) (if (equal? x v) i (loop (+ 1 i) xs))])))

(define (eqmap eq l . lsts)
  (define len (length l))
  (and (andmap (lambda (l) (= len (length l))) lsts)
       (apply andmap eq l lsts)))

(define (stream-take n s)
  (for/list ([x (in-stream s)]
             [_ (in-range n)])
    x))

(define (stream-append-lazy stream stream-thunk)
  (if (stream-empty? stream) (stream-thunk)
    (stream-cons (stream-first stream)
      (stream-append-lazy (stream-rest stream stream-thunk)))))

(define (freeze-hash h)
  (make-immutable-hash (hash->list h)))

(define (hash-union-with a b f)
  (define keys (set-union (list->set (dict-keys a)) (list->set (dict-keys b))))
  (for/hash ([k keys])
    (values k
      (if (not (dict-has-key? a k))
        (dict-ref b k)
        (if (not (dict-has-key? b k))
          (dict-ref a k)
          (f (dict-ref a k) (dict-ref b k)))))))

(define (hash-intersection-with a b f)
  (for/hash ([k (in-dict-keys a)]
              #:when (dict-has-key? b k))
    (f (dict-ref a k) (dict-ref b k))))
