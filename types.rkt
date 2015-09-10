#lang racket

(require "util.rkt" "ast.rkt")
(provide (all-defined-out))

;; Type manipulation
(struct type-error exn:fail:user () #:transparent)
(define (type-error! msg) (raise (type-error msg (current-continuation-marks))))

(define/match (subtype? a b)
  [((t-sum a) (t-sum b))
    (for/and ([(name type) (in-dict a)])
      (and (dict-has-key? b name)
           (subtype? type (dict-ref b name))))]
  [((t-set a) (t-set b)) (subtype? a b)]
  [((t-tuple a) (t-tuple b)) (subtypes? a b)]
  [((t-fun ax ay) (t-fun bx by)) (and (subtype? bx ax) (subtype? ay by))]
  [((t-rel ax ay) (t-rel bx by)) (and (subtype? bx ax) (subtype? ay by))]
  [((t-bot) _) #t]
  [(a b) (equal? a b)])

(define (subtypes? as bs) (eqmap subtype? as bs))

;;; least upper bound of two types. errors if types have no lub.
(define/match (type-lub l r)
  [((t-bot) x) x]
  [(x (t-bot)) x]
  [((t-set a) (t-set b)) (t-set (type-lub a b))]
  [((t-fun ax ay) (t-fun bx by)) (arrow-type-lub t-fun ax bx ay by)]
  [((t-rel ax ay) (t-rel bx by)) (arrow-type-lub t-rel ax bx ay by)]
  [((t-tuple a) (t-tuple b)) (t-tuple (type-lubs a b "tuple length mismatch"))]
  [((t-sum a) (t-sum b)) (hash-union-with a b type-lub)]
  [(a b) (cond
           [(subtype? a b) b]
           [(subtype? b a) a]
           [#t (type-error! (format "could not unify ~v and ~v" a b))])])

(define (arrow-type-lub type-ctor ax bx ay by)
  (define x (type-glbs ax bx "parameter length mismatch"))
  (when (member (t-bot) x) (warn! "argument of type bot"))
  (type-ctor x (type-lub ay by)))

;;; greatest lower bound of two types. always exists b/c of (t-bot), although
;;; this is rather degenerate :/.
(define (type-glb l r)
  (with-handlers ([type-error? (lambda (e) (t-bot))])
    (match* (l r)
      [((t-set a) (t-set b)) (t-set (type-glb a b))]
      [((t-fun ax ay) (t-fun bx by)) (t-fun (type-lubs ax bx) (type-glb ay by))]
      [((t-rel ax ay) (t-rel bx by)) (t-rel (type-lubs ax bx) (type-glb ay by))]
      [((t-tuple a) (t-tuple b)) (t-tuple (type-glbs a b))]
      [((t-sum a) (t-sum b)) (hash-intersection-with a b type-glb)]
      [(a b) (cond
               [(subtype? a b) a]
               [(subtype? b a) b]
               [#t (t-bot)])])))

(define (type-lubs ls rs [msg #f])
  (if (= (length ls) (length rs)) (map type-lub ls rs)
    (type-error! (or msg "type list length mismatch"))))

(define (type-glbs ls rs [msg #f])
  (if (= (length ls) (length rs)) (map type-glb ls rs)
    (type-error! (or msg "type list length mismatch"))))

(define (types-lub l) (foldl type-lub (t-bot) l))
