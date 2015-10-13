#lang racket

(require "util.rkt" "sets.rkt" "multiset.rkt" "queue.rkt")

;; TODO: think carefully about semantics of input & output messages. should they
;; be multisets, not queues? that would be more in line with linear logic, and
;; could always tag them with unique ids to recover time ordering.

;; linear is a dict from symbols to multisets of tuples
;; view is a dict from symbols to sets of tuples
;; inbox & outbox are queues of head-tuples
;; view can also be #f, for "uninitialized"
(struct state (linear [view #:mutable] inbox outbox) #:transparent)

;; a linear "state transition" rule
(struct state-rule (exvars inputs outputs conditions) #:transparent)

;; a datalog-style "view" rule
(struct view-rule (exvars head body) #:transparent)

(struct program
  ;; {state,view,input,output}-preds are sets of symbols.
  ;; state-rules is a set of state-rules.
  ;; view-rules is a dict mapping view-pred symbols to sets of rules.
  (state-preds view-preds input-preds output-preds
   state-rules view-rules)
  #:transparent)

;; a transition is a state rule to apply plus a substitution. a substition is a
;; dict mapping the exvars of the state rule to ground terms.
(struct transition (state-rule substitution) #:transparent)

;; finds the set of transitions that fire.
(define (transitions program state)
  (error "unimplemented"))

(define (apply-transition program state transition)
  (error "unimplemented"))

;; applies transitions until there are no more to apply.
;; currently errors if there is any nondeterminism.
;; FIXME: think harder about nondeterminism.
;;
;; returns: (values new-state list-of-transitions)
(define (quiesce program state) (error "unimplemented"))

;; returns: new-state
(define (send message program st)
  (match-define (state l v i o) st)
  (state l v (queue-push message i) o))

;; returns: (values new-state message)
(define (recv program st [on-empty (lambda () (error "no message to recv"))])
  (match-define (state l v i o) st)
  (define-values (new-o msg) (queue-pop o on-empty))
  (values (state l v i new-o) msg))

;; returns: (values new-state message-list)
;; message-list has most recent output message first.
(define (recv-all program st)
  (match-define (state l v i o) st)
  (values (state l v i empty-queue) (queue->list o)))
