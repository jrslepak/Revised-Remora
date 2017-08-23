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
   [==> ((array {natural_f-frm ...}
                [atom:t_fn ...]
                : (Array (-> [(Array type_in idx_in) ...] type_out) idx_fn))
         (array {natural_arg ...}
                [atom:t_arg ...]
                : (Array type_in idx_arg))
         ...
         : type_app)
        ((array {natural_p-frm ...}
                [atom:t_f-rep ...]
                : (Array (-> [(Array type_in idx_in) ...] type_out)
                         {Shp natural_p-frm ...}))
         (array {natural_a-frm ... natural_a-exp ... natural_in ...}
                [atom:t_a-rep ...]
                : (Array type_in {Shp natural_a-frm ...
                                      natural_a-exp ...
                                      natural_in ...}))
         ...
         : type_app)
        ;; Frames:
        ;; -  {natural_f-frm ...}      (function position frame)
        ;; - [{natural_a-frm ...} ...] (argument position frames)
        ;; -  {natural_p-frm ...}      (principal frame)
        (where [{Shp natural_a-frm ...} ...]
          [(drop-suffix idx_in idx_arg) ...])
        (where {Shp natural_p-frm ...}
          (largest-frame [{Shp natural_f-frm ...} {Shp natural_a-frm ...} ...]))
        ;; Require that at least one component frame be different from the
        ;; principal frame -- otherwise, take a map or β step instead.
        ;; Why doesn't the check work if written like this?
        #;(where [_ ... #f _ ...] (term [(idx=? {Shp natural_f-frm ...}
                                                {Shp natural_p-frm ...})
                                         (idx=? {Shp natural_a-frm ...}
                                                {Shp natural_p-frm ...}) ...]))
        (side-condition
         (not (term (all [(idx=? {Shp natural_f-frm ...}
                                 {Shp natural_p-frm ...})
                          (idx=? {Shp natural_a-frm ...}
                                 {Shp natural_p-frm ...}) ...]))))
        ;; Expansions:
        ;; -  {natural_f-exp ...}      (function position expansion)
        ;; - [{natural_a-exp ...} ...] (argument position expansions)
        (where {Shp natural_f-exp ...}
          (drop-prefix {Shp natural_f-frm ...} {Shp natural_p-frm ...}))
        (where [{Shp natural_a-exp ...} ...]
          [(drop-prefix {Shp natural_a-frm ...} {Shp natural_p-frm ...}) ...])
        (where natural_f-ratio (nprod {natural_f-exp ...}))
        (where [natural_a-ratio ...] [(nprod {natural_a-exp ...}) ...])
        ;; Cell sizes:
        ;; - 1 (function cell)
        ;; - [(* natural_in ...) ...] (argument cells)
        (where [{Shp natural_in ...} ...]
          [(normalize-idx idx_in) ...])
        (where [(atom:t_f-cell) ...] (split [atom:t_fn ...] 1))
        (where [[(atom:t_a-cell ...) ...] ...]
          [(split [atom:t_arg ...] (nprod {natural_in ...})) ...])
        (where [atom:t_f-rep ...]
          (concat ((replicate (atom:t_f-cell) natural_f-ratio) ...)))
        ;; A bit of manual lifting trickery because ellipses won't really line
        ;; up in the right way on their own
        (where ((natural_replic ...) ...)
          ((copies natural_a-ratio (length/m [(atom:t_a-cell ...) ...])) ...))
        (where [[atom:t_a-rep ...] ...]
          [(concat ((replicate (atom:t_a-cell ...) natural_replic) ...)) ...])
        lift]
   [==> ((array {natural_fn ...} ; In a map redex, all frames are the same.
                [atom:t_fn ...]
                : (Array (-> [(Array type_in idx_in) ...] type_out) _))
         (array {natural_arg ...}
                [atom:t_arg ...]
                : (Array type_arg idx_arg))
         ... : type_app)
        (frame {natural_fn ...}
               [((array {} [atom:t_fn]
                        : (Array (-> [(Array type_in idx_in) ...] type_out)
                                 {Shp}))
                 expr:t_argcell ...
                 : type_out)
                ...]
               : type_app)
        (side-condition (< 0 (length (term {natural_fn ...}))))
        (where [{Shp natural_acell ...} ...]
          [(drop-prefix {Shp natural_fn ...} {Shp natural_arg ...}) ...])
        ;; A map requires all cell shapes to match the function's input types.
        (where #t (all [(idx=? idx_in {Shp natural_acell ...}) ...]))
        (where [natural_csize ...] [(nprod {natural_acell ...}) ...])
        ;; Build the (nested) list of cells from each array, then transpose it
        ;; to get the lists of cells that go to each app in the result frame.
        (where [[[atom:t_argcell ...] ...] ...]
          (transpose/m [(split [atom:t_arg ...] natural_csize) ...]))
        (where [[expr:t_argcell ...] ...]
          [[(array {natural_acell ...} [atom:t_argcell ...]
                   : (Array type_in idx_in)) ...] ...])
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
