#lang racket

(require "util.rkt" "sets.rkt"
  "ast.rkt" "types.rkt" "elab.rkt"
  "parse.rkt" "eval.rkt" "compile.rkt")

;;; Putting it all together
(define (run expr)
  (printf "expr: ~v\n" expr)

  (define-values (type elab-expr) (elab '() expr))
  (define level (car elab-expr))
  (printf "type: ~a\n" (pretty-format type))
  [printf "elab: ~v\n" elab-expr]

  (printf "val:  ") (pretty-write ((if (F? level) eval-F eval-R) '() elab-expr))

  (define code ((if (F? level) compile-F compile-R) elab-expr '()))
  (printf "code: ") (pretty-write (syntax->datum code))
  (printf "val:  ") (pretty-write (eval code)))

(define (repl)
  (printf "> ")
  (define input (read))
  (unless (eof-object? input)
    (with-handlers ([exn:fail? print-error])
      (run (parse input)))
    (repl)))

(define test-expr
  '(case (union 2 3)
     (2 "two") (3 "three") (_ (union "hello" "fux"))))

(define (test [test-expr test-expr])
  (define e (parse test-expr))
  (define-values (t ee) (elab '() e))
  (pretty-write (syntax->datum (compile-R ee '()))))
