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
     (TApp E type)
     (IApp E idx)
     (Box idx E)
     (Unbox (var var E) expr:t)
     (Unbox (var var val:t) E)))

(define ->R
  (reduction-relation
   Remora-exec
   #:domain expr:t
   ;; Redex forms:
   ;; - (op val)
   ;; - ((λ ___) val)
   ;; -- subcase: lift
   [==> ((Arr [scal:t_fn ...] {natural_f-frm ...}
              : [([type_in {Shp natural_in ...}] -> type_out) idx_fn])
         (Arr [scal:t_arg ...] {natural_a-frm ... natural_in ...} : [type_in idx_arg])
         : type_app)
        ;; Cell sizes:
        ;; - 1 (function cell)
        ;; - (* natural_in ...) (argument cell)
        ;; TODO: side condition to ensure arg position has principal frame
        ;; TODO: Make how many copies of each function cell?
        ((Arr [scal:t_f-rep ...]
              {natural_p-frm ...}
              : [([type_in {Shp natural_in ...}] -> type_out)
                 {Shp natural_p-frm ...}])
         (Arr [scal:t_a-rep ...]
              {natural_a-frm ... natural_a-exp ... natural_in ...}
              : [type_in {Shp natural_a-frm ... natural_a-exp ... natural_in ...}])
         : type_app)
        ;; Frames:
        ;; - {natural_ff ...} (function position frame)
        ;; - {natural_af ...} (argument position frame)
        ;; - {natural_pf ...} (principal frame)
        (where {natural_p-frm ...} (prefix-max {natural_f-frm ...} {natural_a-frm ...}))
        ;; Require that at least one component frame be different from the
        ;; principal frame -- otherwise, take a map or β step instead.
        (side-condition (not (and (equal? (term {natural_p-frm ...})
                                          (term {natural_f-frm ...}))
                                  (equal? (term {natural_p-frm ...})
                                          (term {natural_a-frm ...})))))
        ;; Expansions:
        ;; - {natural_fe ...} (function position expansion)
        ;; - {natural_ae ...} (argument position expansion)
        (where {natural_f-exp ...} (prefix-sub {natural_p-frm ...} {natural_f-frm ...}))
        (where {natural_a-exp ...} (prefix-sub {natural_p-frm ...} {natural_a-frm ...}))
        (where natural_f-ratio (nprod {natural_f-exp ...}))
        (where natural_a-ratio (nprod {natural_a-exp ...}))
        ;; Cell sizes:
        ;; - 1 (function cell)
        ;; - (* natural_in ...) (argument cell)
        (where [(scal:t_f-cell) ...] (split [scal:t_fn ...] 1))
        (where [(scal:t_a-cell ...) ...] (split [scal:t_arg ...]
                                                (nprod {natural_in ...})))
        (where [scal:t_f-rep ...]
          (concat ((replicate (scal:t_f-cell) natural_f-ratio) ...)))
        (where [scal:t_a-rep ...]
          (concat ((replicate (scal:t_a-cell ...) natural_a-ratio) ...)))
        lift]
   ;; -- subcase: map
   [==> ((Arr [scal:t_fn ...] {natural_fn ...}
              : (([type_in {Shp natural_arg ...}] -> type_out) idx_fn))
         (Arr [scal:t_arg ...] {natural_fn ... natural_arg ...} : type_arg)
         : type_app)
        (Arr [(scal:t_fn expr:t_argcell : type_out) ...] {natural_fn ...} : type_app)
        (where [(scal:t_argcell ...) ...]
          (split [scal:t_arg ...] (nprod {natural_arg ...})))
        (where [expr:t_argcell ...]
          [(Arr [scal:t_argcell ...] {natural_arg ...}
                : [type_in {Shp natural_arg ...}])
           ...])
        map]
   ;; -- subcase: β
   [==> ((λ var expr:t : ((type_in -> type_out) {Shp})) val:t : type_app)
        (substitute expr:t var val:t)
        (where (_ : type_arg) val:t)
        (side-condition (judgment-holds (type-eqv type_in type_out)))
        β]
   ;; - (TApp (Tλ ___) type)
   [==> (TApp (Tλ var expr:t : type_tlam) type_arg : type_tapp)
        (substitute expr:t var type_arg)
        Tβ]
   ;; - (TApp (Arr (val ...) __)) type)
   [==> (TApp (Arr [scal:t ...] {natural ...}
                              : ((∀ var type_univ) idx_shp))
              type_arg
              : type_tapp)
        (Arr [(TApp scal:t type_arg
                    : (substitute type_univ var type_arg)) ...]
             {natural ...}
             : type_tapp)
        TMap]
   ;; - (IApp (Iλ ___) idx)
   [==> (IApp (Iλ var sort expr:t : type_ilam) idx_arg : type_iapp)
        (substitute expr:t var idx_arg)
        Iβ]
   ;; - (IApp (Arr ((Iλ ___) ...) __)) type)
   [==> (IApp (Arr [scal:t ...] {natural ...}
                              : ((Π var sort type_pi) idx_shp))
              idx_arg
              : type_iapp)
        (Arr [(IApp scal:t idx_arg
                    : (substitute type_pi var idx_arg)) ...]
             {natural ...}
             : type_iapp)
        IMap]
   ;; - (Unbox (___ (Box)) ___)
   ;; - (Arr ((Arr ___) ...) ___)
   with
   [(--> (in-hole E a) (in-hole E b))
    (==> a b)]))

(module+ test
  (check-equal? (apply-reduction-relation
                 ->R
                 (term ((Arr [(mean : [([Int {Shp 3}] -> [Int {Shp}]) {Shp}])]
                             {}
                             : [([Int {Shp 3}] -> [Int {Shp}]) {Shp}])
                        (Arr [4 3 2 1 0 -1] {2 3} : [Int {Shp 2 3}])
                        : [Int {Shp 2}])))
                (list
                 (term
                  ((Arr [(mean : [([Int {Shp 3}] -> [Int {Shp}]) {Shp}])
                         (mean : [([Int {Shp 3}] -> [Int {Shp}]) {Shp}])]
                        {2}
                        : [([Int {Shp 3}] -> [Int {Shp}]) {Shp 2}])
                   (Arr [4 3 2 1 0 -1] {2 3} : [Int {Shp 2 3}])
                   : [Int {Shp 2}]))))
  (check-equal? (apply-reduction-relation
                 ->R
                 (term (TApp (Arr [(x : (&∀ [t] (&-> [t] t)))
                                   (y : (&∀ [t] (&-> [t] t)))
                                   (z : (&∀ [t] (&-> [t] t)))]
                                  {3}
                                  : ((∀ t (&-> [t] t)) {Shp 3}))
                             Int : ((Int -> Int) {Shp 3}))))
                (list
                 (term
                  (Arr [(TApp (x : (&∀ [t] (&-> [t] t))) Int
                              : (&-> [Int] Int))
                        (TApp (y : (&∀ [t] (&-> [t] t))) Int
                              : (&-> [Int] Int))
                        (TApp (z : (&∀ [t] (&-> [t] t))) Int
                              : (&-> [Int] Int))]
                       {3}
                       : ((Int -> Int) {Shp 3})))))

  (check-equal? (apply-reduction-relation
                 ->R
                 (term ((Arr [(mean : [([Int {Shp 3}] -> [Int {Shp}]) {Shp}])
                              (mean : [([Int {Shp 3}] -> [Int {Shp}]) {Shp}])]
                             {2}
                             : [([Int {Shp 3}] -> [Int {Shp}]) {Shp 2}])
                        (Arr [4 3 2 1 0 -1] {2 3} : [Int {Shp 2 3}])
                        : [Int {Shp 2}])))
                (list
                 (term
                  (Arr [((mean : (((Int (Shp 3)) -> (Int (Shp))) (Shp)))
                         (Arr (4 3 2) (3) : (Int (Shp 3))) : (Int (Shp)))
                        ((mean : (((Int (Shp 3)) -> (Int (Shp))) (Shp)))
                         (Arr (1 0 -1) (3) : (Int (Shp 3))) : (Int (Shp)))]
                       {2}
                       : [Int {Shp 2}])))))

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
  [(replicate any natural) (concat (any (replicate any ,(sub1 (term natural)))))])
(module+ test
  (check-equal? (term (replicate (a 3 #f) 4))
                (term (a 3 #f a 3 #f a 3 #f a 3 #f))))
