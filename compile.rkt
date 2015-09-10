#lang racket

(require "util.rkt" "ast.rkt" "eval.rkt" "elab.rkt" "sets.rkt")
(provide (all-defined-out))

;;; Compilation to Racket
(define (compile-F level-expr env)
  (define (recur x) (compile-F x env))
  (match-define (cons level expr) level-expr)
  (unless (F? level) (error "internal error: got R, expected F"))
  (match expr
    [(e-base v _) #`'#,v]
    [(e-var _ i) (env-ref env i)]
    [(e-set e) (compile-R env e)]
    [(e-tuple es) #`(make-tuple #,@(map recur es))]
    [(e-proj i e) #`(tuple-ref #,(recur e) '#,i)]
    [(e-tag tag e) #`(make-tag tag #,(recur e))]
    [(e-case subj branches)
      #`(let ((subject #,(recur subj)))
          #,(compile-case #'subject compile-F branches env))]
    [(e-app-fun func args) #`(#,(recur func) #,@(map recur args))]
    [(e-fun vs _ body)
      (define syms (map gensym vs))
      #`(lambda (#,@syms) #,(compile-F body (env-extend syms env)))]
    [(e-rel vs _ body)
      (define syms (map gensym vs))
      #`(lambda (#,@syms) #,(compile-R body (env-extend syms env)))]
    [_ (error "internal error: not an F expression")]))

(define (compile-R level-expr env)
  (define (recur x) (compile-R x env))
  (match-define (cons level expr) level-expr)
  (if (F? level)
    #`(set #,(compile-F level-expr env))
    (match expr
      [(e-empty) #'(set)]
      [(e-union a b) #`(set-union #,(recur a) #,(recur b))]
      [(e-any e) (match (car e)
                   ['F (compile-F e env)]
                   ['R #`(set-unions #,(recur e))])]
      [(e-tuple es) #`(set-call make-tuple #,(map recur es))]
      [(e-proj i e) #`(for/set ([x #,(recur e)]) (tuple-ref x '#,i))]
      [(e-tag tag e) #`(for/set ([x #,(recur e)]) (make-tag '#,tag x))]
      [(e-case subj branches)
        (define cont (compile-case #'subject compile-R branches env))
        (match (car subj)
          ['F #`(let ((subject #,(compile-F subj env))) #,cont)]
          ['R #`(let*/set ((subject #,(recur subj))) #,cont)])]
      [(e-app-fun func args) (compile-app-R func args env #'for/set)]
      [(e-app-rel func args) (compile-app-R func args env #'let*/set)]
      [_ (error "internal error: not an R expression")])))

(define (compile-case subject-expr compiler branches env)
  #`(match #,subject-expr
      #,@(for/list ([b branches])
           (match-define (cons p e) b)
           (define-values (racket-pat more-env) (compile-pat p env))
           #`[#,racket-pat #,(compiler e (env-extend more-env env))])))

(define (compile-app-R func args env form)
  ;; here we take advantage of order of evaluation being unspecified.
  (define terms (for/list ([t (cons func args)]) (cons (gensym) t)))
  (define-values (fs rs) (partition (compose F? cadr) terms))
  #`(let #,(for/list ([f fs]) (list (car f) (compile-F (cdr f) env)))
      (#,form #,(for/list ([r rs]) (list (car r) (compile-R (cdr r) env)))
        #,(map car terms))))

;; compile-pat : pat (list-of sym) -> racket-pat (list-of sym)
(define (compile-pat pat env)
  (match pat
    [(p-wild) (values #'_ '())]
    [(p-var name) (let ((x (gensym name))) (values x (list x)))]
    [(p-tuple ps)
      (define-values (racket-pats envs)
        (for/lists (pats envs) ([p ps]) (compile-pat p env)))
      (values #`(vector #,@racket-pats) (append* envs))]
    [(p-tag tag p)
      (define-values (racket-pat env) (compile-pat p env))
      (values #`(list '#,tag #,racket-pat) env)]
    [(p-lit l) (values #`'#,l '())]))
