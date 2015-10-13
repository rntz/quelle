#lang racket

(provide
  queue? empty-queue queue-empty? queue-push queue-pop queue-peek queue->list)

;; immutable queues.
(struct queue (ins outs) #:transparent)

(define empty-queue (queue '() '()))

(define (queue-empty? q)
  (and (null? (queue-ins q)) (null? (queue-outs q))))

(define (queue-push x q)
  (match q
    [(queue xs ys) (queue (cons x xs) ys)]))

;; returns (values new-q removed-value)
(define (queue-pop q [on-empty (lambda () (error "empty queue"))])
  (match q
    [(queue '() '()) (values q (on-empty))]
    [(queue xs '()) (queue-pop (queue '() (reverse xs)))]
    [(queue xs (cons y ys)) (values (queue xs ys) y)]))

;; TODO: this operation is asymptotically inefficient if used repeatedly, which
;; we ignore for now. :(
(define (queue-peek q [on-empty (lambda () (error "empty queue"))])
  (define-values (_ x) (queue-pop q on-empty))
  x)

;; produces list with next-to-pop first, most-recently-pushed last.
(define (queue->list q)
  (append (queue-outs q) (reverse (queue-ins q))))
