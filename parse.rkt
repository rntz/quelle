#lang racket

(require "util.rkt" "ast.rkt"
  "elab.rkt" ;; for env-extend.
  )
(provide (all-defined-out))

;;; Parsing s-expressions as exprs.
;;; this parser is a gross hack.
(define (parse e [env '()])
  ;; (printf "parse ~a ~a\n" e env)
  (define (recur x) (parse x env))
  (match e
    [(? lit? x) (e-base x (lit-type x))]
    ['empty (e-empty)]
    [`(union ,a ,b) (e-union (recur a) (recur b))]
    [`(set ,a) (e-set (recur a))]
    [`(any ,a)  (e-any (recur a))]
    [`(list . ,es) (e-tuple (map recur es))]
    [`(get ,(? number? index) ,a) (e-proj index (recur a))]
    [(or `(tag ,(? symbol? name) ,a)
         `((,'quote ,(? symbol? name)) ,a))
      (e-tag name (recur a))]
    [`(case ,subj (,ps ,es) ...)
      (e-case (recur subj)
        (for/list ([p ps] [e es])
          (define pat (parse-pat p env))
          (define value (parse e (env-extend (pat-vars pat) env)))
          (cons pat value)))]
    [`(fn (,vs ,ts) ... ,body)
      (set! ts (map parse-type ts))
      (e-fun vs ts (parse body (env-extend vs env)))]
    [`(fn . ,_) (error "fn what now")]
    [`(rel (,vs ,ts) ... ,body)
      (set! ts (map parse-type ts))
      (e-rel vs ts (parse body (env-extend vs env)))]
    [(or `(app ,f . ,as) `(,f . ,as))
      (e-app (recur f) (map recur as))]
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
    [`(sum (,names ,types) ...)
      (t-sum (for/hash ([name names] [type types])
               (values name (parse-type type))))]
    [`(,xs ... -> ,y) (t-fun (map parse-type xs) (parse-type y))]
    [`(,xs ... => ,y) (t-rel (map parse-type xs) (parse-type y))]))

(define (parse-pat pat env)
  (match pat
    ['_ (p-wild)]
    [(? lit? l) (p-lit l)]
    [(or `(tag ,tag-name ,p)`(',(? symbol? tag-name) ,p))
      (p-tag tag-name (parse-pat p env))]
    [(? symbol? name) (p-var name)]
    [(or `(list . ,ps) (? list? ps))
      (p-tuple (map (lambda (x) (parse-pat x env)) ps))]))

(define (pat-vars pat)
  (match pat
    [(or (p-wild) (p-lit _)) '()]
    [(p-var name) (list name)]
    [(p-tuple ps) (append* (map pat-vars ps))]
    [(p-tag _ p) (pat-vars p)]))

;(define builtins '(((+ - * / =) (num num -> num))))
