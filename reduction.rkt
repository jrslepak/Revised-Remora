#lang racket

(require redex
         "language.rkt"
         "typing-rules.rkt")

(module+ test
  (require rackunit))

(define-extended-language Remora-exec Remora-annotated
  (E hole
     (E expr:t)
     (val:t E)
     (t-app E type : type)
     (i-app E idx : type)
     (box idx ... E : type)
     (unbox (var ... var E) expr:t : type)
     (unbox (var ... var val:t) E : type)))

(define ->R
  (reduction-relation
   Remora-exec
   #:domain expr:t
   ;; TODO: try shortened version of lift rule, as scribbled in notebook
   [==> ((array {natural_ff ...}
                [atom:t_f ...]
                : (Array (-> [(Array type_in {Shp natural_in ...}) ...]
                             type_out)
                         {Shp natural_ff ...}))
         (array {natural_af ... natural_in ...}
                [atom:t_a ...]
                : (Array type_in {Shp natural_af ... natural_in ...}))
         ...
         : type_app)
        ((array {natural_pf ...}
                (concat (replicate-each
                         (split [atom:t_f ...] (nprod {natural_ff ...}))
                         natural_fe))
                : (Array (-> [(Array type_in {Shp natural_in ...}) ...]
                             type_out)
                         {Shp natural_pf ...}))
         (array {natural_pf ... natural_in ...}
                (concat (replicate-each
                         (split [atom:t_a ...] (nprod {natural_in ...}))
                         natural_ae))
                : (Array type_in {Shp natural_pf ... natural_in ...}))
         ...
         : type_app)
        (where {Shp natural_pf ...}
          (largest-frame [{Shp natural_ff ...} {Shp natural_af ...} ...]))
        (side-condition
         (not (term (all [(idx=?
                           {Shp natural_pf ...} {Shp natural_ff ...})
                          (idx=?
                           {Shp natural_pf ...} {Shp natural_af ...}) ...]))))
        (where [natural_fe natural_ae ...]
          [(nprod/s
            (drop-prefix {Shp natural_ff ...} {Shp natural_pf ...}))
           (nprod/s
            (drop-prefix {Shp natural_af ...} {Shp natural_pf ...})) ...])
        (where [(any_cell ...) ...]
          ((split [atom:t_a ...] (nprod {natural_in ...})) ...))
        lift]
   [==> ((array {natural_f ...}
                [atval:t_f ...]
                : (Array (-> [(Array type_in {Shp natural_in ...}) ...]
                             type_out)
                         {Shp natural_f ...}))
         (array {natural_f0 ... natural_in ...}
                [atval:t_a ...]
                : (Array type_in {Shp natural_f0 ... natural_in ...}))
         ...
         : type_app)
        (frame {natural_f ...}
               [((array {} [atval:t_f]
                        : (Array (-> [(Array type_in {Shp natural_in ...}) ...]
                                     type_out)
                                 {Shp}))
                 (array {natural_in ...}
                        [atval:t_cell ...]
                        : (Array type_in {Shp natural_in ...}))
                 ...
                 : type_out) ...]
               : type_app)
        (where #t (all [(idx=? {Shp natural_f ...} {Shp natural_f0 ...}) ...]))
        (side-condition (< 0 (length (term {natural_f ...}))))
        (where (((atval:t_cell ...) ...) ...)
          (transpose/m ((split [atval:t_a ...] (nprod {natural_in ...})) ...)))
        map]
   [==> ((array {} [(λ [var ...] expr:t : type_00)]
                : (Array (-> [type_in ...] type_01) {Shp}))
         val:t ... : type_app)
        (subst:t* expr:t [(var val:t) ...])
        (where [type_in ...]
          [(expr:t->type val:t) ...])
        β]
   [==> (t-app (array {natural ...}
                      [(tλ [var ...] expr:t : _) ...]
                      : _)
               type_arg ...
               : type_tm)
        (frame {natural ...}
               [(subst* expr:t [(var type_arg) ...]) ...]
               : type_tm)
        t-β]
   [==> (i-app (array {natural ...}
                      [(iλ [var ...] expr:t : _) ...]
                      : _)
               idx_arg ...
               : type_tm)
        (frame {natural ...}
               [(subst* expr:t [(var idx_arg) ...]) ...]
               : type_tm)
        i-β]
   ;; TODO: δ
   [==> (frame {_ ...}
               [(array {_ ...} [atval:t ...] : _) ...]
               : (Array type {Shp natural ...}))
        (array {natural ...}
               (concat ([atval:t ...] ...))
               : (Array type {Shp natural ...}))
        collapse]
   [==> (unbox (var_i ... var_e
                      (array {} [(box idx ... expr:t_box : type_box)] : _))
          expr:t_body : type_out)
        (subst* (subst:t expr:t_body var_e expr:t_box)
                [(var_i idx) ...])
        let-box]
   with
   [(--> (in-hole E a) (in-hole E b))
    (==> a b)]))

(module+ test
  ;;; Specify the expected inputs and outputs in non-elaborated form
  (define (check-under-elaboration f)
    (λ (in #:env [env '(() () ())] outs)
      (define s (first env)) (define k (second env)) (define t (third env))
      (define elaborated-input (term (elaborate/env ,s ,k ,t ,in)))
      (define results (f elaborated-input))
      (define unannotated-results (map (λ (t) (term (unelaborate ,t))) results))
      (check (λ (got wanted)
               (alpha-equivalent? Remora-exec got wanted))
             unannotated-results outs)))
  (define check-step
    (check-under-elaboration
     (λ (input) (apply-reduction-relation ->R input))))
  (define check-step*
    (check-under-elaboration
     (λ (input) (apply-reduction-relation* ->R input))))
  ;;; Scalar type application
  (check-step
   (term (t-app (scl (tλ [(T Atom)] (scl (λ [(x (Array T {Shp}))] x)))) Int))
   (list (term (frame {} [(scl (λ [(x (Array Int {Shp}))] x))]))))
  ;;; Lifted type application
  (check-step
   (term (t-app (array {3}
                       [(tλ [(T Atom)] (scl (λ [(x (Array T {Shp}))] x)))
                        (tλ [(T Atom)] (scl (λ [(x (Array T {Shp}))] x)))
                        (tλ [(T Atom)] (scl (λ [(x (Array T {Shp}))] x)))])
                Int))
   (list
    (term (frame {3} [(scl (λ [(x (Array Int {Shp}))] x))
                      (scl (λ [(x (Array Int {Shp}))] x))
                      (scl (λ [(x (Array Int {Shp}))] x))]))))
  ;;; Scalar index application
  (check-step
   (term (i-app (scl (iλ [(S Shape)] (scl (λ [(x (Array Int S))] x))))
                {Shp 4 7}))
   (list
    (term (frame {} [(scl (λ [(x (Array Int {Shp 4 7}))] x))]))))
  ;;; Lifted index application
  (check-step
   (term (i-app (array {2}
                       [(iλ [(S Shape)] (scl (λ [(x (Array Int S))] x)))
                        (iλ [(S Shape)] (scl (λ [(x (Array Int S))] x)))])
                {Shp 3 3}))
   (list
    (term (frame {2} [(scl (λ [(x (Array Int {Shp 3 3}))] x))
                      (scl (λ [(x (Array Int {Shp 3 3}))] x))]))))
  ;;; Lift reduction
  (check-step
   (term ((array {} [+])
          (array {3 2} [1 2 3 4 5 6])
          (array {3} [9 8 7])))
   (list (term ((array {3 2} [+ + + + + +])
                (array {3 2} [1 2 3 4 5 6])
                (array {3 2} [9 9 8 8 7 7])))))
  ;;; Map reduction
  (check-step
   (term ((array {3} [(λ [(x (Array Int {Shp 2}))
                          (y (Array Int {Shp 2}))]
                        ((scl +) x y))
                      (λ [(x (Array Int {Shp 2}))
                          (y (Array Int {Shp 2}))]
                        ((scl +) x y))
                      (λ [(x (Array Int {Shp 2}))
                          (y (Array Int {Shp 2}))]
                        ((scl +) x y))])
          (array {3 2} [1 2 3 4 5 6])
          (array {3 2} [9 8 7 6 5 4])))
   (list
    (term (frame {3} [((scl (λ [(x (Array Int {Shp 2}))
                                (y (Array Int {Shp 2}))] ((scl +) x y)))
                       (array {2} [1 2])
                       (array {2} [9 8]))
                      ((scl (λ [(x (Array Int {Shp 2}))
                                (y (Array Int {Shp 2}))] ((scl +) x y)))
                       (array {2} [3 4])
                       (array {2} [7 6]))
                      ((scl (λ [(x (Array Int {Shp 2}))
                                (y (Array Int {Shp 2}))] ((scl +) x y)))
                       (array {2} [5 6])
                       (array {2} [5 4]))]))))
  ;;; β reduction
  (check-step
   (term ((scl (λ [(x (Scl Int))
                   (y (Scl Int))]
                 ((scl +) x y)))
          (scl 10) (scl 20)))
   (list (term ((scl +) (scl 10) (scl 20)))))
  ;;; δ reduction
  ;;; Collapse reduction
  (check-step
   (term (frame {5} [(array {2} [0 1])
                     (array {2} [2 3])
                     (array {2} [4 5])
                     (array {2} [6 7])
                     (array {2} [8 9])]))
   (list (term (array {5 2} [0 1 2 3 4 5 6 7 8 9]))))
  ;;; Let-box reduction
  (check-step
   (term (unbox [l a (scl (box 3 (array {2 3} [1 2 3 4 5 6])
                               (Σ [(d Dim)] (Array Int {Shp 2 d}))))]
           ((i-app (t-app (scl length) Int) l {Shp}) a)))
   (list (term ((i-app (t-app (scl length) Int) 3 {Shp})
                (array {2 3} [1 2 3 4 5 6]))))))


(define-metafunction Remora-exec
  expr:t->type : expr:t -> type
  [(expr:t->type (_ ... : type)) type])
(define-metafunction Remora-exec
  atom:t->type : atom:t -> type
  [(atom:t->type (_ ... : type)) type]
  [(atom:t->type  atom)
   type
   (where (type) ,(judgment-holds (type-of/atom () () () atom type _) type))])

(define-metafunction Remora-exec
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

;;; Select larger argument (according to the prefix partial order)
(define-metafunction Remora-exec
  prefix-max : {natural ...} {natural ...} -> {natural ...} ∪ #f
  [(prefix-max {natural_0 ... natural_1 ...} {natural_0 ...})
   {natural_0 ... natural_1 ...}]
  [(prefix-max {natural_0 ...} {natural_0 ... natural_1 ...})
   {natural_0 ... natural_1 ...}]
  [(prefix-max _ _) #f])
;;; Find the difference according to prefix ordering (i.e., remove the longest
;;; shared prefix from the larger argument)
;;; n.b., this is written to be commutative
(define-metafunction Remora-exec
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

;;; Numeric product of list of naturals, because we do this a lot
(define-metafunction Remora-exec
  nprod : (natural ...) -> natural
  [(nprod (natural ...)) ,(foldr * 1 (term (natural ...)))])
;;; Numeric product of a shape
(define-metafunction Remora-exec
  nprod/s : {Shp natural ...} -> natural
  [(nprod/s {Shp natural ...}) (nprod (natural ...))])

;;; Boolean product of a list
(define-metafunction Remora-exec
  all : (boolean ...) -> boolean
  [(all (_ ... #f _ ...)) #f]
  [(all _) #t])

;;; Append many lists
(define-metafunction Remora-exec
  concat : ((any ...) ...) -> (any ...)
  [(concat ()) ()]
  [(concat ((any ...))) (any ...)]
  [(concat ((any_0 ...) (any_1 ...) (any_2 ...) ...))
   (concat ((any_0 ... any_1 ...)  (any_2 ...) ...))])

;;; Make many replicas of a list
(define-metafunction Remora-exec
  replicate : (any ...) natural -> (any ...)
  [(replicate _ 0) ()]
  [(replicate any natural)
   (concat (any (replicate any ,(sub1 (term natural)))))])
(module+ test
  (check-equal? (term (replicate (a 3 #f) 4))
                (term (a 3 #f a 3 #f a 3 #f a 3 #f))))
;;; Make many replicas of each element in a list
(define-metafunction Remora-exec
  replicate-each : (any ...) natural -> (any ...)
  [(replicate-each (any ...) natural) (concat ((copies any natural) ...))])

;;; Make a list with many of something
(define-metafunction Remora-exec
  copies : any natural -> (any ...)
  [(copies any natural)
   ,(for/list ([i (term natural)]) (term any))])

;;; Find the length of a term list
(define-metafunction Remora-exec
  length/m : (any ...) -> natural
  [(length/m (any ...)) ,(length (term (any ...)))])

;;; Transpose a list-of-lists
(define-metafunction Remora-exec
  transpose/m : ((any ...) ...) -> ((any ...) ...)
  [(transpose/m ()) ()]
  [(transpose/m (() ...)) ()]
  [(transpose/m ((any_0 any_1 ...) ...))
   ,(cons (term (any_0 ...))
          (term (transpose/m ((any_1 ...) ...))))])
