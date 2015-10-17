#lang racket

(require "util.rkt")

(provide
  reverse-graph
  (struct-out graph) (struct-out node) (struct-out state)
  eval-func/c same-func/c
  make-state quiesce! run-node!)

;; generic and useful utility:
;; reverses an adjacency-set representation of a graph
(define/contract (reverse-graph g)
  (->
    (hash/c any/c (set/c any/c #:kind 'dont-care) #:immutable 'dont-care)
    (hash/c any/c (set/c any/c #:kind 'dont-care) #:immutable 'dont-care))
  (define reversed (make-hash))
  (for ([(k vs) g])
    (for ([v vs])
      (hash-update! reversed v
        (lambda (x) (set-add! x k) x)
        (lambda () (mutable-set)))))
  ;; mutability police! freeze!
  (for/hash ([(k v) reversed])
    (values k (freeze-set v))))


;;; ---------- DATAFLOW GRAPHS ----------

;; nodes: maps node ids to node structures.
;; depends: maps node id N to the node ids of nodes it depends on.
;; dependees: maps node id N to the node ids of nodes depending on N.
(struct graph (nodes depends dependees) #:transparent)

;; eval: function that calculates the node's value.
;; same: function that determines if node value is unchanged.
;; depends: node IDs this node depends on.
(struct node (eval same) #:transparent)

;;; A state of the dataflow graph.
(struct state
  ;; dirty is a mutable set of node ids.
  ;; values is a mutable hash from node ids to their values.
  (dirty values)
  #:transparent)

;; A node function takes a hash from node ids to their current values; and
;; produces a new value for the node.
(define eval-func/c (-> (hash/c symbol? any/c) any/c))

;; A same function takes the old and new values and determines if there's
;; been a change.
(define same-func/c (-> any/c any/c boolean?))


;;; ---------- DATAFLOW GRAPH INTERPRETER ----------
;; init-value is a function from node ids to their initial values.
(define/contract (make-state graph init-value)
  (-> graph? (-> symbol? any/c) state?)
  (define node-ids (hash-keys (graph-nodes graph)))
  (state
    ;; initially everything's dirty
    (list->mutable-set node-ids)
    (make-hash
      (for/list ([n node-ids])
        (cons n (init-value n))))))

;; runs nodes in graph until all nodes are clean.
(define (quiesce! g s)
  (define dirty (state-dirty s))
  (unless (set-empty? dirty)
    ;; pick a node "at random" & run it.
    (run-node! g s (set-first dirty))
    ;; keep going.
    (quiesce! g s)))

;; re-runs node unconditionally.
;; does not check whether node is dirty.
;; clears node's dirty state and dirties its dependees as appropriate.
(define (run-node! g s node-id)
  (printf "RUN: ~a\n" node-id)
  (match-define (graph nodes depends dependees) g)
  (match-define (state dirty vals) s)
  (match-define (node eval-func same-func) (hash-ref nodes node-id))
  (define old-val (hash-ref vals node-id))
  (define new-val (eval-func vals))
  ;; if we same, we have work to do.
  (unless (same-func old-val new-val)
    ;; update our value & dirty our dependees
    (hash-set! vals node-id new-val)
    (set-union! dirty (hash-ref dependees node-id)))
  ;; clear our node
  (set-remove! dirty node-id))
