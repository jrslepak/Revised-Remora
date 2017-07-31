#lang racket

(require redex
         "language.rkt")
(provide Remora-annotated
         sort-of kind-of type-of type-eqv idx->*
         elaborate elaborate/env unelaborate)

(module+ test
  (require rackunit))

;;; ___:t versions of Remora abstract syntax include a type annotation on each
;;; expression, so that the type information is readily available for the
;;; reduction semantics. Using an extended language rather than a completely
;;; separate language means primops, base values, and environment structure can
;;; be reused as is, and metafunctions can cross between "multiple" languages.
;;; TODO: add and test new binding form declarations for λ, Tλ, Iλ
(define-extended-language Remora-annotated Remora-explicit
  (expr:t scal:t
          (Arr (expr:t ...) (natural ...) : type)
          (expr:t expr:t : type)
          (TApp expr:t type : type)
          (IApp expr:t idx : type)
          (Box idx expr:t : type)
          (Unbox (var var expr:t) expr:t : type))
  (scal:t base-val
          op
          var:t
          (λ var expr:t : type)
          (Tλ var expr:t : type)
          (Iλ var sort expr:t : type))
  (val:t scal:t
         (Arr (scal:t ...) (natural ...) : type))
  (var:t (var : type)))

(define-judgment-form Remora-explicit
  #:mode (sort-of I I O)
  #:contract (sort-of sort-env idx sort)
  [(sort-of (_ ... [var sort] _ ...) var sort)
   sort-var]
  [(sort-of _ natural Dim)
   sort-nat]
  [(sort-of sort-env idx Dim) ...
   --- sort-shp
   (sort-of sort-env {Shp idx ...} Shape)]
  [(sort-of sort-env idx Dim) ...
   --- sort-plus
   (sort-of sort-env {+ idx ...} Dim)]
  [(sort-of sort-env idx Shape) ...
   --- sort-append
   (sort-of sort-env {++ idx ...} Shape)])

(define-judgment-form Remora-explicit
  #:mode (kind-of I I I O)
  #:contract (kind-of sort-env kind-env type kind)
  [(kind-of _ (_ ... [var kind] _ ...) var kind)
   kind-var]
  [(kind-of _ _ base-type (Shape -> ★))
   kind-base]
  [(kind-of sort-env kind-env type_in ★)
   (kind-of sort-env kind-env type_out ★)
   --- kind-fn
   (kind-of sort-env kind-env (type_in -> type_out) (Shape -> ★))]
  [(kind-of sort-env ([var (Shape -> ★)] kind-bind ...) type (Shape -> ★))
   --- kind-all
   (kind-of sort-env (kind-bind ...) (∀ var type) (Shape -> ★))]
  [(kind-of ([var sort] sort-bind ...) kind-env type (Shape -> ★))
   --- kind-pi
   (kind-of (sort-bind ...) kind-env (Π var sort type) (Shape -> ★))]
  [(kind-of ([var sort] sort-bind ...) kind-env type (Shape -> ★))
   --- kind-sigma
   (kind-of (sort-bind ...) kind-env (Σ var sort type) (Shape -> ★))]
  [(kind-of sort-env kind-env type (sort -> kind))
   (sort-of sort-env idx sort)
   --- kind-app
   (kind-of sort-env kind-env (type idx) kind)])

;;; Type-check an expression in a given environment. One output position is the
;;; type of the given term. The other is a fully-annotated version of the term.
(define-judgment-form Remora-annotated
  #:mode (type-of I I I I O O)
  #:contract (type-of sort-env kind-env type-env expr type expr:t)
  [(type-of _ _ (_ ... [var type] _ ...) var type (var : type))
   type-var]
  [(type-of _ _ _ op (op->type op) op)
   type-op]
  [(type-of _ _ _ integer (Int {Shp}) integer)
   type-int]
  [(type-of _ _ _ boolean (Bool {Shp}) boolean)
   type-bool]
  [(type-of sort-env kind-env type-env expr_elt (type_elt idx_elt) expr:t_elt)
   ;(side-condition ,(printf "Lead element has type ~v\n" (term (type_elt idx_elt))))
   (type-of sort-env kind-env type-env expr_rest (type_rest idx_rest) expr:t_rest) ...
   ;; Ensure every type derived from expr_1 ... is equivalent to the type
   ;; derived from expr_0.
   (type-eqv (type_elt idx_elt) (type_rest idx_rest)) ...
   ;; Ensure number of elements fits with specified shape.
   ;; Phrasing this as an index equality check (on naturals) makes it appear
   ;; when building a derivation tree.
   (idx-eqv ,(length (term (expr_elt expr_rest ...)))
            ,(foldr * 1 (term (natural ...))))
   (where type_result (type_elt (normalize-idx {++ {Shp natural ...} idx_elt})))
   --- type-array
   (type-of sort-env kind-env type-env
            (Arr (expr_elt expr_rest ...) {natural ...})
            type_result
            (Arr (expr:t_elt expr:t_rest ...) (natural ...)
                 : type_result))]
  ;;;; TODO: update these rules to generate the fully-annotated term
  [;; Type annotation must be an element type, not just sub-array type (i.e., no
   ;; "nested empty" arrays).
   (kind-of sort-env kind-env type (Shape -> ★))
   (where type_result (type {Shp natural_0 ... 0 natural_1 ...}))
   --- type-empty
   (type-of sort-env kind-env type-env
            (Arr type {natural_0 ... 0 natural_1 ...})
            type_result
            (Arr () (natural_0 ... 0 natural_1 ...)
                 : type_result))]
  [(type-of sort-env kind-env ([var type_in] type-bind ...)
            expr type_out expr:t)
   (kind-of sort-env kind-env
            type_out ★)
   (where type_result ((type_in -> type_out) {Shp}))
   --- type-fn
   (type-of sort-env kind-env (type-bind ...)
            (λ var type_in expr) type_result
            (λ var expr:t : type_result))]
  [(type-of sort-env ([var (Shape -> ★)] kind-bind ...) type-env
            expr type expr:t)
   (kind-of sort-env (kind-bind ...)
            type ★)
   (where type_result (∀ var type))
   --- type-Tfn
   (type-of sort-env (kind-bind ...) type-env
            (Tλ var expr) type_result
            (Tλ var expr:t : type_result))]
  [(type-of ([var sort] sort-bind ...) kind-env type-env
            expr type expr:t)
   (kind-of ([var sort] sort-bind ...) kind-env
            type ★)
   (where type_result (Π var sort type))
   --- type-Ifn
   (type-of (sort-bind ...) kind-env type-env
            (Iλ var sort expr) type_result
            (Iλ var sort expr:t : type_result))]
  [#;(side-condition ,(printf "Trying type-app\n"))
   (type-of sort-env kind-env type-env
            expr_fn type_fnposn expr:t_fn)
   #;(side-condition ,(printf "Got type ~v in function position\n"
                            (term type_fnposn)))
   (where (((type_in idx_cell-in)
            -> (type_out idx_cell-out)) idx_ffr)
     type_fnposn)
   (type-of sort-env kind-env type-env
            expr_arg (type_in idx_arg) expr:t_arg)
   ;; Identify the argument frame (the function position's frame is its
   ;; entire shape).
   (where idx_afr (frame-contribution idx_cell-in idx_arg))
   ;; Compare with function frame to choose principal frame.
   (where idx_pr (larger-frame idx_ffr idx_afr))
   (where type_result (type_out idx_pr))
   --- type-app
   (type-of sort-env kind-env type-env
            (expr_fn expr_arg)
            type_result
            (expr:t_fn expr:t_arg : type_result))]
  [(type-of sort-env kind-env type-env
            expr
            ((∀ var (type_univ idx_result)) idx_frame)
            expr:t)
   (kind-of sort-env kind-env type_arg (Shape -> ★))
   (sort-of sort-env idx_frame Shape)
   (where type_result
     (substitute (type_univ (normalize-idx {++ idx_frame idx_result}))
                 var type_arg))
   -- type-TApp
   (type-of sort-env kind-env type-env
            (TApp expr type_arg)
            type_result
            (TApp expr:t type_arg : type_result))]
  ;; TODO: Test to make sure this is building things up right.
  [(type-of sort-env kind-env type-env
            expr
            ((Π var sort (type idx_result)) idx_frame)
            expr:t)
   (sort-of sort-env idx_arg sort)
   (sort-of sort-env idx_frame Shape)
   (where type_result
     (substitute (type (normalize-idx {++ idx_frame idx_result}))
                 var idx_arg))
   -- type-IApp
   (type-of sort-env kind-env type-env
            (IApp expr idx_arg)
            ;; TODO: Make sure substitute won't accidentally change anything in
            ;; idx_fn (this should be safe if it respects binding properly
            ;; because var cannot be bound in idx_fn).
            type_result
            (IApp expr:t idx_arg : type_result))]
  [(sort-of sort-env idx sort)
   (type-of sort-env kind-env type-env
            expr (substitute type var idx) expr:t)
   --- type-box
   (type-of sort-env kind-env type-env
            (Box idx expr (Σ var sort type)) (Σ var sort type)
            (Box idx expr : (Σ var sort type)))]
  [(type-of (sort-bind ...) kind-env (type-bind ...)
            expr_box (Σ var_sum sort type_sum) expr:t_box)
   (type-of ([var_i sort] sort-bind ...)
            kind-env
            ([var_e (substitute type_sum var_sum var_i)] type-bind ...)
            expr_result type_result expr:t_result)
   (kind-of (sort-bind ...) kind-env
            type_result ★)
   --- type-unbox
   (type-of (sort-bind ...) kind-env (type-bind ...)
            (Unbox (var_i var_e expr_box) expr_result)
            type_result
            (Unbox (var_i var_e expr:t_box) expr:t_result : type_result))])

(module+ test
  ;; Variable type lookup
  (check-equal?
   (judgment-holds
    (type-of () ()
             ([mean [([Int {Shp 3}] -> [Int {Shp}]) {Shp}]])
             mean type expr:t)
    (type expr:t))
   (list (term ([([Int {Shp 3}] -> [Int {Shp}]) {Shp}]
                (mean : [([Int {Shp 3}] -> [Int {Shp}]) {Shp}])))))
  ;; Index application for an array of index-polymorphic functions
  (check-not-false
   (redex-match
    Remora-explicit
    [(((Int {Shp 5}) -> ((Σ var Shape (Int var)) {Shp})) {Shp 3 2})]
    (judgment-holds
     (type-of [][][]
              (Arr [(IApp (Arr (iota iota) (2)) 5)
                    (IApp (Arr (iota iota) (2)) 5)
                    (IApp (Arr (iota iota) (2)) 5)]
                   [3])
              type _)
     type)))
  ;; Fully apply an array of iotas (to get an array of boxes)
  (check-not-false
   (redex-match
    Remora-explicit
    (((Σ var_s Shape (Int var_s)) (Shp 2)))
    (judgment-holds
     (type-of [][][]
              ((IApp (Arr (iota iota) (2)) 3) (Arr (2 3 4) (3)))
              type _)
     type))))

;;; Stub code for type/idx equivalence judgments -- syntactic equality for now
(define-judgment-form Remora-explicit
  #:mode (type-eqv I I)
  #:contract (type-eqv type type)
  [(type-eqv type type)])
(define-judgment-form Remora-explicit
  #:mode (idx-eqv I I)
  #:contract (idx-eqv idx idx)
  [(idx-eqv idx idx)])

;;; Reduction on type indices
(define-judgment-form Remora-explicit
  #:mode (idx->* I O)
  #:contract (idx->* idx idx)
  [(idx->* natural natural)]
  [(idx->* var var)]
  [(idx->* idx_old idx_new) ...
   ---
   (idx->* {Shp idx_old ...}
           {Shp idx_new ...})]
  [(idx->* idx_old idx_reduced) ...
   (where (idx_new ...) (summand-order (idx_reduced ...)))
   ---
   (idx->* {+ idx_old ...}
           {+ idx_new ...})]
  [(idx->* idx_old idx_new) ...
   ---
   (idx->* {++ idx_old ...}
           {++ idx_new ...})])

;;; Metafunction wrappers for type-of judgment which produces the fully annotated
;;; version of a closed term (elaborate) or possibly open terms (elaborate/env)
(define-metafunction Remora-annotated
  elaborate/env : sort-env kind-env type-env expr -> expr:t
  [(elaborate/env sort-env kind-env type-env expr)
   expr:t_out
   (where (expr:t_out _ ...)
     ,(judgment-holds
       (type-of sort-env kind-env type-env expr _ expr:t)
       expr:t))])
(define-metafunction Remora-annotated
  elaborate : expr -> expr:t
  [(elaborate expr) (elaborate/env () () () expr)])

;;; Convert fully annotated term to minimally annotated form
(define-metafunction Remora-annotated
  unelaborate : expr:t -> expr
  [(unelaborate base-val) base-val]
  [(unelaborate op) op]
  [(unelaborate (var : type)) var]
  [(unelaborate (λ var expr:t : ((type_in -> _) _)))
   (λ var type_in (unelaborate expr:t))]
  [(unelaborate (Tλ var expr:t : _))
   (Tλ var (unelaborate expr:t))]
  [(unelaborate (Iλ var sort expr:t : _))
   (λ var sort (unelaborate expr:t))]
  [(unelaborate (Arr [expr:t ...] {natural_0 ... 0 natural_1} : [type _]))
   (Arr type {natural_0 ... 0 natural_1})]
  [(unelaborate (Arr [expr:t ...] {natural ...} : type))
   (Arr [(unelaborate expr:t) ...] {natural ...})]
  [(unelaborate (expr:t_f expr:t_a : type))
   ((unelaborate expr:t_f) (unelaborate expr:t_a))]
  [(unelaborate (TApp expr:t type : _))
   (TApp (unelaborate expr:t) type)]
  [(unelaborate (IApp expr:t idx : _))
   (IApp (unelaborate expr:t) idx)]
  [(unelaborate (Box idx expr:t : type))
   (Box idx expr:t type)]
  [(unelaborate (Unbox (var_i var_e expr:t_box) expr:t_body : type))
   (Unbox (var_i var_e (unelaborate expr:t_box)) (unelaborate expr:t_body))])

;;; Pass expected shape and actual shape. This metafunction assumes the indices
;;; passed in are well-formed Shapes. Returns the frame shape if it exists.
;;; Otherwise, return false.
(define-metafunction Remora-explicit
  frame-contribution : idx idx -> idx ∪ #f
  [(frame-contribution {Shp} idx) idx]
  [(frame-contribution idx idx) {Shp}]
  ;; TODO: Loosen this pattern to allow guaranteed-equal indices in idx_0 rather
  ;; than only syntactically identical indices.
  [(frame-contribution {Shp idx_0 ...}
                       {Shp idx_1 ... idx_0 ...})
   {Shp idx_1 ...}]
  ;; TODO: Handle append.
  #;[(frame-contribution {++ idx_0 ...}
                         {++ idx_1 ...})
     ....]
  ;; Two different variables are not provably equal. (If both vars are the same,
  ;; it will be caught by an earlier case.)
  [(frame-contribution var var) #f]
  [(frame-contribution _ _) #f])

;;; Identify which frame has the other as a prefix. Return false if neither one
;;; is prefixed by the other.
;;; TODO: Allow looser than exact syntactic match, like for frame-contribution.
(define-metafunction Remora-explicit
  larger-frame : idx idx -> idx ∪ #f
  [(larger-frame {Shp} idx) idx]
  [(larger-frame idx {Shp}) idx]
  [(larger-frame idx idx) idx]
  [(larger-frame {Shp idx_0 ...}
                 {Shp idx_0 ... idx_1 ...})
   {Shp idx_0 ... idx_1 ...}]
  [(larger-frame {Shp idx_0 ... idx_1 ...}
                 {Shp idx_0 ...})
   {Shp idx_0 ... idx_1 ...}]
  [(larger-frame _ _) #f])


;;; TODO: summand-order metafunction (this is stub code)
;;; Move the summands from an index into canonical order. Lead with a single
;;; literal nat (or elide it if it would be 0), and follow with variables in
;;; lexicographic order.
(define-metafunction Remora-explicit
  summand-order : (idx ...) -> (idx ...)
  [(summand-order any) any])

;;; Reduce a type index to a canonical normal form.
(define-metafunction Remora-explicit
  normalize-idx : idx -> idx
  [(normalize-idx natural) natural]
  [(normalize-idx {Shp idx ...})
   {Shp (normalize-idx idx) ...}]
  [(normalize-idx var) var]
  [(normalize-idx {++ idx ...})
   idx_n
   (where {idx_n} (merge-append {(normalize-idx idx) ...}))]
  [(normalize-idx {++ idx ...})
   {++ idx_n ...}
   (where (idx_n ...) (merge-append {(normalize-idx idx) ...}))])
(define-metafunction Remora-explicit
  merge-append : {idx ...} -> {idx ...}
  [(merge-append {idx_0 ... {++ idx_s ...} idx_1 ...})
   (merge-append {idx_0 ... idx_s ... idx_1 ...})]
  [(merge-append {idx_0 ... {Shp idx_s0 ...} {Shp idx_s1 ...} idx_1 ...})
   (merge-append {idx_0 ... {Shp idx_s0 ... idx_s1 ...} idx_1 ...})]
  [(merge-append any) any])
(define-metafunction Remora-explicit
  ;; Three things can appear inside a (well-formed) sum:
  ;; - natural
  ;; - variable
  ;; - sum
  ;; The canonical form for a sum is flattened, with all variables in
  ;; lexicographic order and a single natural number at the front (or no
  ;; natural number literals at all).
  merge-plus : {idx ...} -> {idx ...}
  ;; Flatten any nested sums
  [(merge-plus {idx_0 ... {+ idx_1 ...} idx_2 ...})
   (merge-plus {idx_0 ... idx_1 ... idx_2 ...})]
  ;; If there are at least two numeric literals, add and move them to the front
  [(merge-plus {idx_0 ... natural_0 idx_1 ... natural_1 idx_2 ...})
   (merge-plus {,(+ (term natural_0)
                    (term natural_1))
                idx_0 ... idx_1 ... idx_2 ...})]
  ;; For just one numeric literal, move it to the front
  [(merge-plus {idx_0 ... natural idx_1 ...})
   (merge-plus {natural idx_0 ... idx_1 ...})]
  ;; If these cases are reached, we should have only variables and possibly one
  ;; numeric literal remaining
  [(merge-plus {natural var ...})
   (merge-plus ,(cons (term natural)
                      (sort (λ (l r) (string<=? (symbol->string l)
                                                (symbol->string r)))
                            (term {var ...}))))]
  [(merge-plus {var ...})
   (merge-plus ,(sort (λ (l r) (string<=? (symbol->string l)
                                          (symbol->string r)))
                 (term {var ...})))])
