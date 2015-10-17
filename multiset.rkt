#lang racket

(require "util.rkt" "sets.rkt")

(provide
  multiset? multiset
  multiset-count multiset-contains? multiset-empty? multiset-size
  multiset-add multiset-remove
  multiset-union multiset-subtract submultiset?
  multiset->hash multiset->list multiset->set)

;; elements is a hash mapping elements to their counts.
;; invariant: all counts are positive.
;; (an element with 0 count should be removed from the hash)
(struct mset (counts) #:transparent
  #:property prop:sequence (lambda (ms) (mset-counts ms)))

(define multiset? mset?)

(define (multiset . xs)
  (define h (make-hash))
  (for ([x xs])
    (hash-update! h x (lambda (v) (+ 1 v)) (lambda () 0)))
  (mset (freeze-hash h)))

(define empty-multiset (multiset))

(define (multiset-empty? m) (hash-empty? (mset-counts m)))

(define (multiset-count ms k)
  (hash-ref (mset-counts ms) k 0))

(define (multiset-contains? ms k)
  (> 0 (multiset-count ms k)))

(define (multiset-size ms)
  (for/sum ([(k count) ms])
    count))

(define (multiset-add ms k [n 1])
  (assert! (>= n 0))
  (if (= n 0)
    ms
    (mset (hash-update (mset-counts ms) k
            (lambda (x) (+ x n))
            (lambda () 0)))))

(define (multiset-remove ms k)
  (define h (mset-counts ms))
  (match (multiset-count ms k)
    [0 ms]
    [1 (mset (hash-remove h k))]
    [n (mset (hash-update h (lambda (v) (- v 1))))]))

(fn multiset-union
  [() empty-multiset]
  [(x) x]
  [((mset x) (mset y)) (mset (hash-union-with x y +))]
  [(x . ys) (foldl multiset-union x ys)])

(define (multiset-subtract a b)
  (if (multiset-empty? b) a             ;optimization
    (mset
      (for/hash ([(k v) a]
                  #:when (> 0 (- v (multiset-count b k))))
        (values k (- v (multiset-count b k)))))))

(define (submultiset? a b)
  (for/and ([(k v) a])
    (<= v (multiset-count b k))))

(define (multiset->hash ms) (mset-counts ms))

(define (multiset->list ms)
  (for*/list ([(k count) ms]
              [_ count])
    k))

(define (multiset->set ms)
  (list->set (hash-keys (multiset->hash ms))))
