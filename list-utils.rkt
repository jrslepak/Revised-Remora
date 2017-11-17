#lang racket

(require redex
         "language.rkt")
(provide transpose/m
         split
         nprod nprod/s
         replicate replicate-each
         copies
         concat
         prefix-max prefix-sub)

(module+ test (require rackunit))

;;;; +---------------------------------------+
;;;; | List-processing utility metafunctions |
;;;; +---------------------------------------+

;;; Transpose a list-of-lists
(define-metafunction Remora-explicit
  transpose/m : ((any ...) ...) -> ((any ...) ...)
  [(transpose/m ()) ()]
  [(transpose/m (() ...)) ()]
  [(transpose/m ((any_0 any_1 ...) ...))
   ,(cons (term (any_0 ...))
          (term (transpose/m ((any_1 ...) ...))))])
;; Break a list into segments of specified length
(define-metafunction Remora-explicit
  split : [any ...] natural -> [[any ...] ...]
  [(split [] _) []]
  [(split [any ...] natural)
   [[any ...]]
   (side-condition (< (length (term [any ...])) (term natural)))]
  [(split [any ...] natural)
   ,(cons (take (term [any ...]) (term natural))
          (term (split ,(drop (term [any ...]) (term natural)) natural)))])
(module+ test
  (check-equal? (term (split [a b c d e f g h] 2))
                (term [[a b] [c d] [e f] [g h]]))
  (check-equal? (term (split [a b c d e f g h] 3))
                (term [[a b c] [d e f] [g h]]))
  (check-equal? (term (split [a b c d e f g h] 4))
                (term [[a b c d] [e f g h]])))
;;; Numeric product of list of naturals, because we do this a lot
(define-metafunction Remora-explicit
  nprod : (natural ...) -> natural
  [(nprod (natural ...)) ,(foldr * 1 (term (natural ...)))])
;;; Numeric product of a shape
(define-metafunction Remora-explicit
  nprod/s : {Shp natural ...} -> natural
  [(nprod/s {Shp natural ...}) (nprod (natural ...))])
;;; Make many replicas of a list
(define-metafunction Remora-explicit
  replicate : (any ...) natural -> (any ...)
  [(replicate _ 0) ()]
  [(replicate any natural)
   (concat (any (replicate any ,(sub1 (term natural)))))])
(module+ test
  (check-equal? (term (replicate (a 3 #f) 4))
                (term (a 3 #f a 3 #f a 3 #f a 3 #f))))
;;; Make many replicas of each element in a list
(define-metafunction Remora-explicit
  replicate-each : (any ...) natural -> (any ...)
  [(replicate-each (any ...) natural) (concat ((copies any natural) ...))])
;;; Make a list with many of something
(define-metafunction Remora-explicit
  copies : any natural -> (any ...)
  [(copies any natural)
   ,(for/list ([i (term natural)]) (term any))])
;;; Append many lists
(define-metafunction Remora-explicit
  concat : ((any ...) ...) -> (any ...)
  [(concat ()) ()]
  [(concat ((any ...))) (any ...)]
  [(concat ((any_0 ...) (any_1 ...) (any_2 ...) ...))
   (concat ((any_0 ... any_1 ...)  (any_2 ...) ...))])
;;; Select larger argument (according to the prefix partial order)
(define-metafunction Remora-explicit
  prefix-max : {natural ...} {natural ...} -> {natural ...} ∪ #f
  [(prefix-max {natural_0 ... natural_1 ...} {natural_0 ...})
   {natural_0 ... natural_1 ...}]
  [(prefix-max {natural_0 ...} {natural_0 ... natural_1 ...})
   {natural_0 ... natural_1 ...}]
  [(prefix-max _ _) #f])
;;; Find the difference according to prefix ordering (i.e., remove the longest
;;; shared prefix from the larger argument)
;;; n.b., this is written to be commutative
(define-metafunction Remora-explicit
  prefix-sub : {natural ...} {natural ...} -> {natural ...} ∪ #f
  [(prefix-sub {natural_0 ... natural_1 ...} {natural_0 ...})
   {natural_1 ...}]
  [(prefix-sub {natural_0 ...} {natural_0 ... natural_1 ...})
   {natural_1 ...}]
  [(prefix-sub _ _) #f])
(module+ test
  (check-equal? (term (prefix-max {3 5 4 2} {3 5})) (term {3 5 4 2}))
  (check-equal? (term (prefix-max {3 5 4} {3 5})) (term {3 5 4}))
  (check-equal? (term (prefix-max {2 6 7} {2 6 7 9})) (term {2 6 7 9}))
  (check-equal? (term (prefix-max {2 6 7} {2 7 9})) (term #f))
  (check-equal? (term (prefix-sub {3 5 4 2} {3 5})) (term {4 2}))
  (check-equal? (term (prefix-sub {3 5 4} {3 5})) (term {4}))
  (check-equal? (term (prefix-sub {2 6 7} {2 6 7 9})) (term {9}))
  (check-equal? (term (prefix-sub {2 6 7} {2 7 9})) (term #f)))
;;; Find the length of a term list
(define-metafunction Remora-explicit
  length/m : (any ...) -> natural
  [(length/m (any ...)) ,(length (term (any ...)))])

