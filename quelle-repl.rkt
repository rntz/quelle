#lang racket

(require "util.rkt" "quelle.rkt")

(define the-program #f)
(define the-state #f)

(define all-kinds '(view state input output))
(define (kind? x) (member x all-kinds))

(define (parse-program sexps)
  ;; set up state
  (define pred-kinds (make-hash))
  (define state-rules (mutable-set))
  (define views (make-hash))

  ;; predicate kind inference
  (define (pred-kinds! pred kinds)
    (hash-update! pred-kinds pred
      (lambda (ks) (set-intersect ks kinds))
      (lambda () all-kinds)))

  (define (pred-kind! pred kind)
    (pred-kinds! pred (list kind)))

  ;; parsing rules
  (define (parse-view-rule pred args conds)
    (pred-kind! pred 'view)
    (define vars ;;TODO
      'VARS
      )
    (hash-update! views pred
      (lambda (s) (set-add s (view-rule vars (cons pred args) conds)))
      (lambda () (set))))

  (define (parse-state-rule pre post side)
    (for ([c pre]) (pred-kinds! (car c) '(state input)))
    (for ([c post]) (pred-kinds! (car c) '(state output)))
    ;; TODO?: maybe side-conditions shouldn't ever be inputs?
    (for ([c side]) (pred-kinds! (car c) '(view state input)))
    (define vars ;;TODO
      'VARS
      )
    (set-add! state-rules (state-rule vars pre post side)))

  ;; parse every declaration
  (for ([decl sexps])
    (match decl
      ;; predicate kind declarations
      [`(,(? kind? k) ,preds ...)
        (for ([p preds]) (pred-kind! p k))]
      ;; rules
      [`((,pred ,args ...) :- ,conds ...)
        (parse-view-rule pred args conds)]
      [`(,pres ... -o ,posts ... if ,conds ...)
        (parse-state-rule pres posts conds)]
      [`(,pres ... -o ,posts ...)
        (parse-state-rule pres posts '())]
      [`(,pred := (,argses ...) ...)
        (for ([args argses])
          (parse-view-rule pred args '()))]
      [_ (error (format "I don't recognize that declaration: ~v" decl))]))

  ;; check that all predicates have possible & unambiguous kinds.
  (define preds
    (for/hash ([(pred ks) pred-kinds])
      (match ks
        [`(,k) (values pred k)]
        ['() (error (format "predicate cannot have any kind: ~v" pred))]
        [_ (error (format (string-append "ambiguous predicate: ~v\n"
                                         "could be any of: ~v")
                    pred ks))])))
  (program preds (freeze-set state-rules) (freeze-hash views)))

(define (load-sexp prog)
  (set! the-program (parse-program prog)))

(define (read-file filename)
  (with-input-from-file filename
    (lambda () (let loop ([acc '()])
            (define x (read))
            (if (eof-object? x)
              (reverse acc)
              (loop (cons x acc)))))))

(define (load-file filename)
  (load-sexp (read-file filename)))

(define (repl)
  (let/ec escape
    (define (quit-repl) (escape (void)))
    (let loop ()
      (match (read)
        [(? eof-object?) (quit-repl)]
        [`(load ,filename) (load-file filename)]
        [_ (displayln "Sorry, I don't understand.")])
      (loop))))
