#lang racket

(require redex
         "language.rkt")
(provide Remora-annotated
         sort-of kind-of type-of/atom type-of/expr type-eqv idx-eqv idx=?
         elaborate elaborate/env unelaborate
         drop-prefix drop-suffix largest-frame
         normalize-idx normalize-indices
         subst* subst:t subst:t*)

(module+ test
  (require rackunit)
  (define-syntax-rule (check-alpha-equivalent? x y)
    (check (λ (l r) (alpha-equivalent? Remora-annotated l r))
           x y)))

;;; ___:t versions of Remora abstract syntax include a type annotation on each
;;; expression, so that the type information is readily available for the
;;; reduction semantics. Using an extended language rather than a completely
;;; separate language means primops, base values, and environment structure can
;;; be reused as is, and metafunctions can cross between "multiple" languages.
;;; TODO: add and test new binding form declarations for λ, Tλ, Iλ
(define-extended-language Remora-annotated Remora-explicit
  (atom:t base-val
          op
          (λ [var ...] expr:t : type)
          (tλ [var ...] val:t : type)
          (iλ [var ...] val:t : type)
          (box idx ... expr:t : type))
  (atval:t base-val
           op
           (λ [var ...] expr:t : type)
           (tλ [var ...] val:t : type)
           (iλ [var ...] val:t : type)
           (box idx ... val:t : type))
  (expr:t var:t
          (array {natural ...} [atom:t ...] : type)
          (frame {natural ...} [expr:t ...] : type)
          (expr:t expr:t ... : type)
          (t-app expr:t type ... : type)
          (i-app expr:t idx ... : type)
          (unbox (var var expr:t) expr:t : type))
  (val:t var:t
         (array (natural ...) (atom:t ...) : type))
  (AE:t atom:t expr:t)
  (var:t (var : type))
  ;; Normalized form of type indices
  (nidx nshp ndim)
  (nshp fshp {++ fshp fshp ...+} {Shp}) ; normalized shape
  (fshp var {Shp ndim ndim ...+}) ; fragment shape
  (ndim aidx {+ aidx aidx ...+}) ; normalized dim
  (aidx var natural) ; atomic index
  #:binding-forms
  (λ [var ...] expr:t #:refers-to (shadow var ...) : type)
  (tλ [var ...] expr:t #:refers-to (shadow var ...) : type)
  (iλ [var ...] expr:t #:refers-to (shadow var ...) : type)
  (unbox (var_i ... var_e expr:t)
    expr:t #:refers-to (shadow var_i ... var_e) : type))


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
  [(kind-of _ _ base-type Atom)
   kind-base]
  [(kind-of sort-env kind-env type_in Array)
   (kind-of sort-env kind-env type_out Array)
   --- kind-fn
   (kind-of sort-env kind-env (type_in -> type_out) Atom)]
  [(kind-of sort-env (update kind-env [(var kind) ...]) type Array)
   --- kind-all
   (kind-of sort-env kind-env (∀ [(var kind) ...] type) Atom)]
  [(kind-of (update sort-env [(var sort) ...]) kind-env type Array)
   --- kind-pi
   (kind-of sort-env kind-env (Π [(var sort) ...] type) Atom)]
  [(kind-of (update sort-env [(var sort) ...]) kind-env type Array)
   --- kind-sigma
   (kind-of sort-env kind-env (Σ [(var sort) ...] type) Atom)]
  [(kind-of sort-env kind-env type Atom)
   (sort-of sort-env idx Shape)
   --- kind-array
   (kind-of sort-env kind-env (Array type idx) Array)])


;;; Type-check an atom in a given environment. One output position is the
;;; type of the given term. The other is a fully-annotated version of the term.
(define-judgment-form Remora-annotated
  #:mode (type-of/atom I I I I O O)
  #:contract (type-of/atom sort-env kind-env type-env atom type atom:t)
  [(type-of/atom _ _ _ op (op->type op) op)
   type-op]
  [(type-of/atom _ _ _ integer Int integer)
   type-int]
  [(type-of/atom _ _ _ boolean Bool boolean)
   type-bool]
  [(type-of/expr sort-env kind-env
                 (update type-env [(var type_in) ...])
                 expr type_out expr:t)
   ;; Function arguments must be Arrays
   (kind-of sort-env kind-env type_in Array) ...
   --- type-fn
   (type-of/atom sort-env kind-env type-env
                 (λ [(var type_in) ...] expr)
                 (-> [type_in ...] type_out)
                 (λ [var ...] expr:t : (-> [type_in ...] type_out)))]
  [(type-of/expr sort-env (update kind-env [(var kind) ...]) type-env
                 expr type expr:t)
   --- type-tfn
   (type-of/atom sort-env kind-env type-env
                 (tλ [(var kind) ...] expr)
                 (∀ [(var kind) ...] type)
                 (tλ [var ...] expr:t
                     : (∀ [(var kind) ...] type)))]
  [(type-of/expr (update sort-env [(var sort) ...]) kind-env type-env
                 expr type expr:t)
   --- type-ifn
   (type-of/atom sort-env kind-env type-env
                 (iλ [(var sort) ...] expr)
                 (Π [(var sort) ...] type)
                 (iλ [var ...] expr:t
                     : (Π [(var sort) ...] type)))]
  [(sort-of sort-env idx sort) ...
   (type-of/expr sort-env kind-env type-env
                 expr type_found expr:t)
   (type-eqv type_found (subst* type [(var idx) ...]))
   --- type-box
   (type-of/atom sort-env kind-env type-env
                 (box idx ... expr (Σ [(var sort) ...] type))
                 (Σ [(var sort) ...] type)
                 (box idx ... expr:t : (Σ [(var sort) ...] type)))])
(module+ test
  ;; Should not allow use of a free type variable
  (check-false
   (judgment-holds
    (type-of/atom [] [] [] (λ [(x (Array A {Shp}))] x) type atom:t)))
  ;; Should not allow use of ill-kinded type
  (check-false
   (judgment-holds
    (type-of/atom [] [(A Array)] []
                  (λ [(x (Array A {Shp}))] x) type atom:t)))
  ;; Type var with Array kind is permissible argument type
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/atom [] [(A Array)] []
                  (λ [(x A)] x) type atom:t)
    (type atom:t))
   (list (term ((-> [A] A) (λ [x] (x : A) : (-> [A] A))))))
  ;; Can build Array-kinded arg type from Atom-kinded type
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/atom [] [(A Atom)] []
                  (λ [(x (Array A {Shp}))] x) type atom:t)
    (type atom:t))
   (list (term ((-> [(Array A {Shp})] (Array A {Shp}))
                (λ [x] (x : (Array A {Shp}))
                  : (-> [(Array A {Shp})] (Array A {Shp})))))))
  ;; As previous case, but put the Atom type into the environment with a tλ
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/atom [] [] []
                  (tλ [(A Atom)] (array {} [(λ [(x (Array A {Shp}))] x)]))
                  type atom:t)
    (type atom:t))
   (list (term ((∀ [(A Atom)]
                   (Array (-> [(Array A {Shp})] (Array A {Shp})) {Shp}))
                (tλ [A] (array {} [(λ [x] (x : (Array A {Shp}))
                                     : (-> [(Array A {Shp})] (Array A {Shp})))]
                               : (Array (-> [(Array A {Shp})] (Array A {Shp}))
                                        {Shp}))
                    : (∀ [(A Atom)]
                         (Array (-> [(Array A {Shp})] (Array A {Shp}))
                                {Shp})))))))
  ;; Make sure iλ puts variables in the environment properly
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/atom [] [] []
                  (iλ [(i Shape)] (array {} [(λ [(x (Array Int i))] x)]))
                  type atom:t)
    (type atom:t))
   (list (term ((Π [(i Shape)] (Array (-> [(Array Int i)] (Array Int i)) {Shp}))
                (iλ [i] (array {}
                               [(λ [x] (x : (Array Int i))
                                  : (-> [(Array Int i)] (Array Int i)))]
                               : (Array (-> [(Array Int i)] (Array Int i))
                                        {Shp}))
                    : (Π [(i Shape)] (Array (-> [(Array Int i)] (Array Int i))
                                            {Shp})))))))
  ;; With the wrong sort for the index argument, this should be ill-typed
  (check-false
   (judgment-holds
    (type-of/atom [] [] []
                  (iλ [(i Dim)] (array {} [(λ [(x (Array Int i))] x)]))
                  type atom:t)))
  ;; Box typed using its actual size
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/atom [] [] []
                  (box 2 (array {2} [2 5]) (Σ [(l Dim)] (Array Int {Shp l})))
                  type atom:t)
    (type atom:t))
   (list (term ((Σ [(l Dim)] (Array Int {Shp l}))
                (box 2 (array {2} [2 5] : (Array Int {Shp 2}))
                     : (Σ [(l Dim)] (Array Int {Shp l})))))))
  ;; Box typed without using its size
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/atom [] [] []
                  (box 15 (array {2} [2 5]) (Σ [(l Dim)] (Array Int {Shp 2})))
                  type atom:t)
    (type atom:t))
   (list (term ((Σ [(l Dim)] (Array Int {Shp 2}))
                (box 15 (array {2} [2 5] : (Array Int {Shp 2}))
                     : (Σ [(l Dim)] (Array Int {Shp 2})))))))
  ;; Box (mis-)typed using the wrong size
  (check-false
   (judgment-holds
    (type-of/atom [] [] []
                  (box 3 (array {2} [2 5]) (Σ [(l Dim)] (Array Int {Shp l})))
                  _ _))))

(define-judgment-form Remora-annotated
  #:mode (type-of/expr I I I I O O)
  #:contract (type-of/expr sort-env kind-env type-env expr type expr:t)
  [(type-of/expr _ _ (_ ... [var type] _ ...) var type (var : type))
   type-var]
  [(type-of/atom sort-env kind-env type-env atom type atom:t)
   ;; Ensure every type derived from remaining atoms is equivalent to the type
   ;; derived from the first one.
   (type-of/atom sort-env kind-env type-env atom_rest type_rest atom:t_rest)
   ...
   (type-eqv type type_rest)
   ...
   ;; Ensure number of elements fits with specified shape.
   ;; Phrasing this as an index equality check (on naturals) makes it appear
   ;; when building a derivation tree.
   (idx-eqv ,(length (term [atom atom_rest ...]))
            ,(foldr * 1 (term {natural ...})))
   --- type-array
   (type-of/expr sort-env kind-env type-env
                 (array {natural ...} [atom atom_rest ...])
                 (Array type {Shp natural ...})
                 (array {natural ...} [atom:t atom:t_rest ...]
                        : (Array type {Shp natural ...})))]
  [(type-of/expr sort-env kind-env type-env
                 expr (Array type_cell idx_cell) expr:t)
   (type-of/expr sort-env kind-env type-env
                 expr_rest type_rest expr:t_rest)
   ...
   (type-eqv (Array type_cell idx_cell) type_rest)
   ...
   (idx-eqv ,(length (term (expr expr_rest ...)))
            ,(foldr * 1 (term (natural ...))))
   --- type-frame
   (type-of/expr sort-env kind-env type-env
                 (frame {natural ...} [expr expr_rest ...])
                 (Array type_cell (normalize-idx
                                   {++ {Shp natural ...} idx_cell}))
                 (frame {natural ...} [expr:t expr:t_rest ...]
                        : (Array type_cell
                                 (normalize-idx
                                  {++ {Shp natural ...} idx_cell}))))]
  [(kind-of sort-env kind-env type Atom)
   (where {_ ... 0 _ ...} {natural ...})
   --- type-emptyA
   (type-of/expr sort-env kind-env type-env
                 (array {natural ...} type)
                 (Array type {Shp natural ...})
                 (array {natural ...} []
                        : (Array type {Shp natural ...})))]
  [(kind-of sort-env kind-env type Atom)
   (where {_ ... 0 _ ...} {natural ...})
   --- type-emptyF
   (type-of/expr sort-env kind-env type-env
                 (frame {natural ...} (Array type idx))
                 (Array type {Shp natural ...})
                 (frame {natural ...} []
                        : (Array type (normalize-idx
                                       {++ {Shp natural ...} idx}))))]
  [(type-of/expr sort-env kind-env type-env
                 expr_fn
                 ;; Identify the input and output cell types.
                 ;; The function's frame (ffr) is its entire shape.
                 (Array (-> [(Array type_in idx_in) ...] (Array type_out idx_out))
                        idx_ffr)
                 expr:t_fn)
   ;; Find the actual arguments' types.
   (type-of/expr sort-env kind-env type-env
                 expr_arg
                 type_actual
                 expr:t_arg)
   ...
   (where ((Array type_arg idx_arg) ...) (type_actual ...))
   (type-eqv type_in type_arg) ...
   ;; Identify each argument's frame.
   (where (idx_afr ...) ((drop-suffix idx_in idx_arg) ...))
   ;; The largest frame is the principal frame.
   (where idx_pfr (largest-frame [idx_ffr idx_afr ...]))
   --- type-app
   (type-of/expr sort-env kind-env type-env
                 (expr_fn expr_arg ...)
                 (Array type_out (normalize-idx {++ idx_pfr idx_out}))
                 (expr:t_fn
                  expr:t_arg ...
                  : (Array type_out (normalize-idx {++ idx_pfr idx_out}))))]
  [(type-of/expr sort-env kind-env type-env
                 expr
                 (Array (∀ [(var kind) ...] (Array type_univ idx_univ))
                        idx_frame)
                 expr:t)
   (kind-of sort-env kind-env type_arg kind) ...
   (where type_subbed
     (normalize-indices
      (subst* (Array type_univ (normalize-idx {++ idx_frame idx_univ}))
              [(var type_arg) ...])))
   --- type-tapp
   (type-of/expr sort-env kind-env type-env
                 (t-app expr type_arg ...)
                 type_subbed
                 (t-app expr:t type_arg ... : type_subbed))]
  [(type-of/expr sort-env kind-env type-env
                 expr
                 (Array (Π [(var sort) ...] (Array type_pi idx_pi))
                        idx_frame)
                 expr:t)
   (sort-of sort-env idx_arg sort) ...
   (where type_subbed
     (normalize-indices
      (subst* (Array type_pi (normalize-idx {++ idx_frame idx_pi}))
              [(var idx_arg) ...])))
   --- type-iapp
   (type-of/expr sort-env kind-env type-env
                 (i-app expr idx_arg ...)
                 type_subbed
                 (i-app expr:t idx_arg ... : type_subbed))]
  [(type-of/expr sort-env kind-env type-env
                 expr_box
                 type_box
                 expr:t_box)
   (where (Array (Σ [(var_sum sort) ...] type_contents) {Shp}) type_box)
   (type-of/expr (update sort-env [(var_i sort) ...])
                 kind-env
                 (update type-env [(var_e (normalize-indices
                                           (subst* type_contents
                                                   [(var_sum var_i) ...])))])
                 expr_body
                 type_body
                 expr:t_body)
   (kind-of sort-env kind-env type_body Array)
   --- type-unbox
   (type-of/expr sort-env kind-env type-env
                 (unbox [var_i ... var_e expr_box] expr_body)
                 type_body
                 (unbox [var_i ... var_e expr:t_box]
                   expr:t_body
                   : type_body))])

(module+ test
  ;; Variable type lookup
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/expr [] []
                  [(mean (Array (-> [(Array Int {Shp 3})] (Array Int {Shp})) {Shp}))]
                  mean type expr:t)
    (type expr:t))
   (list
    (term ((Array (-> [(Array Int {Shp 3})] (Array Int {Shp})) {Shp})
           (mean : (Array (-> [(Array Int {Shp 3})]
                              (Array Int {Shp})) {Shp}))))))
  ;; Index application for scalar
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/expr [] [] []
                  (i-app (array {} [iota]) 5)
                  type expr:t)
    (type expr:t))
   (list (term ((Array (-> [(Array Int {Shp 5})]
                           (Array (Σ [(s Shape)] (Array Int s)) {Shp}))
                       {Shp})
                (i-app (array {} [iota]
                              : (Array (Π [(r Dim)]
                                          (Array (-> [(Array Int {Shp r})]
                                                     (Array (Σ [(s Shape)]
                                                               (Array Int s))
                                                            {Shp}))
                                                 {Shp}))
                                       {Shp}))
                       5
                       : (Array
                          (-> [(Array Int {Shp 5})]
                              (Array (Σ [(s Shape)] (Array Int s)) {Shp}))
                          {Shp}))))))
  ;; Index application for vector
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/expr [] [] []
                  (i-app (array {3} [iota iota iota]) 5)
                  type expr:t)
    (type expr:t))
   (list (term ((Array (-> [(Array Int {Shp 5})]
                           (Array (Σ [(s Shape)] (Array Int s)) {Shp}))
                       {Shp 3})
                (i-app (array {3} [iota iota iota]
                              : (Array (Π [(r Dim)]
                                          (Array (-> [(Array Int {Shp r})]
                                                     (Array (Σ [(s Shape)]
                                                               (Array Int s))
                                                            {Shp}))
                                                 {Shp}))
                                       {Shp 3}))
                       5
                       : (Array
                          (-> [(Array Int {Shp 5})]
                              (Array (Σ [(s Shape)] (Array Int s)) {Shp}))
                          {Shp 3}))))))
  ;; Fully apply an array of iotas (to get an array of boxes)
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/expr [] [] []
                  ((i-app (array {3} [iota iota iota]) 2)
                   (array {3 2} [1 2 3 4 5 6]))
                  type expr:t)
    (type expr:t))
   (list (term ((Array (Σ [(s Shape)] (Array Int s)) {Shp 3})
                ((i-app (array {3} [iota iota iota]
                               : (Array (Π [(r Dim)]
                                           (Array (-> [(Array Int {Shp r})]
                                                      (Array (Σ [(s Shape)]
                                                                (Array Int s))
                                                             {Shp}))
                                                  {Shp}))
                                        {Shp 3}))
                        2
                        : (Array
                           (-> [(Array Int {Shp 2})]
                               (Array (Σ [(s Shape)] (Array Int s)) {Shp}))
                           {Shp 3}))
                 (array {3 2} [1 2 3 4 5 6] : (Array Int {Shp 3 2}))
                 : (Array (Σ [(s Shape)] (Array Int s)) {Shp 3}))))))
  ;; Lifting function that consumes non-scalars
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/expr () () ([f (Array (-> [(Array Int {Shp 2})
                                        (Array Int {Shp 2})]
                                       (Array Int {Shp}))
                                   {Shp})])
                  ((frame {3} [f f f])
                   (array {3 2} [1 2 3 4 5 6])
                   (array {3 2} [9 8 7 6 5 4]))
                  type _)
    type)
   (list (term (Array Int {Shp 3}))))
  ;; Applying primop
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/expr [] [] []
                  ((array {2} [+ *])
                   (array {2 3} [2 3 4 5 6 7])
                   (array {} [10]))
                  type expr:t)
    (type expr:t))
   (list (term ((Array Int {Shp 2 3})
                ((array {2} [+ *] : (Array (-> [(Array Int {Shp})
                                               (Array Int {Shp})]
                                              (Array Int {Shp}))
                                          {Shp 2}))
                 (array {2 3} [2 3 4 5 6 7] : (Array Int {Shp 2 3}))
                 (array {} [10] : (Array Int {Shp}))
                 : (Array Int {Shp 2 3}))))))
  ;; Using the contents of a box
  (check-alpha-equivalent?
   (judgment-holds
    (type-of/expr [] [] []
                  (unbox (sh tensor ((i-app (array {} [iota]) 3)
                                   (array {3} [2 4 5])))
                    ((i-app (t-app (array {} [shape]) Int) sh) tensor))
                  type expr:t)
    (type expr:t))
   (list (term ((Array (Σ [(rank Dim)] (Array Int {Shp rank})) {Shp})
                (unbox (sh
                        tensor
                        ((i-app (array {} [iota]
                                       : (Array
                                          (Π [(r Dim)]
                                             (Array
                                              (-> [(Array Int {Shp r})]
                                                  (Array
                                                   (Σ [(s Shape)]
                                                      (Array Int s))
                                                   {Shp}))
                                              {Shp}))
                                          {Shp}))
                                3
                                : (Array
                                   (-> [(Array Int {Shp 3})]
                                       (Array
                                        (Σ [(s Shape)]
                                           (Array Int s))
                                        {Shp}))
                                   {Shp}))
                         (array {3} [2 4 5] : (Array Int {Shp 3}))
                         : (Array
                            (Σ [(s Shape)]
                               (Array Int s))
                            {Shp})))
                  ((i-app
                    (t-app
                     (array {} [shape]
                            : (Array
                               (∀ [(t Atom)]
                                  (Array
                                   (Π [(s Shape)]
                                      (Array
                                       (-> [(Array t s)]
                                           (Array (Σ [(r Dim)]
                                                     (Array Int {Shp r}))
                                                  {Shp}))
                                       {Shp}))
                                   {Shp}))
                               {Shp}))
                                 Int
                                 : (Array
                                    (Π [(s Shape)]
                                       (Array
                                        (-> [(Array Int s)]
                                            (Array (Σ [(r Dim)]
                                                      (Array Int {Shp r}))
                                                   {Shp}))
                                        {Shp}))
                                    {Shp}))
                          sh
                          : (Array
                             (-> [(Array Int sh)]
                                 (Array (Σ [(r Dim)]
                                           (Array Int {Shp r}))
                                        {Shp}))
                             {Shp}))
                   (tensor : (Array Int sh))
                   : (Array (Σ [(rank Dim)] (Array Int {Shp rank})) {Shp}))
                  : (Array (Σ [(rank Dim)] (Array Int {Shp rank})) {Shp}))))))
  ;; Misuing the contents of a box by letting hidden index info leak out
  (check-false
   (judgment-holds
    (type-of/expr [] [] []
                  (unbox (sh tensor ((i-app (array {} [iota]) 3)
                                   (array {3} [2 4 5])))
                    tensor)
                  type expr:t))))

;;; Stub code for type/idx equivalence judgments -- syntactic equality for now
(define-judgment-form Remora-explicit
  #:mode (type-eqv I I)
  #:contract (type-eqv type type)
  [(side-condition ,(alpha-equivalent?
                     Remora-explicit
                     (term (normalize-indices type_0))
                     (term (normalize-indices type_1))))
   ---
   (type-eqv type_0 type_1)])
(define-judgment-form Remora-explicit
  #:mode (idx-eqv I I)
  #:contract (idx-eqv idx idx)
  [(side-condition ,(equal? (term (normalize-idx idx_0))
                            (term (normalize-idx idx_1))))
   ---
   (idx-eqv idx_0 idx_1)])
(define-metafunction Remora-explicit
  idx=? : idx idx -> boolean
  [(idx=? idx_0 idx_1)
   ,(equal? (term (normalize-idx idx_0))
            (term (normalize-idx idx_1)))
   #;(side-condition (printf "comparing ~v and ~v\n"
                           (term (normalize-idx idx_0))
                           (term (normalize-idx idx_1))))])

;;; Update an environment with new entries (pass original environment first)
(define-metafunction Remora-explicit
  update : [(var any) ...] [(var any) ...] -> [(var any) ...]
  [(update [any_0 ... (var any_old) any_1 ...]
           [any_2 ... (var any_new) any_3 ...])
   (update [any_0 ... (var any_new) any_1 ...]
           [any_2 ... any_3 ...])]
  [(update [any_old ...] [any_new ...]) [any_old ... any_new ...]])
(module+ test
  (check-equal? (term (update [] [])) (term []))
  (check-equal? (term (update [] [(x 3)])) (term [(x 3)]))
  (check-equal? (term (update [(y 4)] [(x 3)]))
                (term [(y 4) (x 3)]))
  (check-equal? (term (update [(y 4)] [(y 3)]))
                (term [(y 3)]))
  (check-equal? (term (update [(y 4) (x 5)] [(y 3)]))
                (term [(y 3) (x 5)]))
  (check-equal? (term (update [(q 9) (y 4) (x 5)] [(y 3)]))
                (term [(q 9) (y 3) (x 5)]))
  (check-equal? (term (update [(q 9) (y 4) (x 5)] [(y 3) (q 12)]))
                (term [(q 12) (y 3) (x 5)]))
  (check-equal? (term (update [(q 9) (y 4) (x 5)] [(y 3) (q 12) (z 0)]))
                (term [(q 12) (y 3) (x 5) (z 0)])))

;;; Substitution for many variables
;;; TODO: does it need to be rewritten to do simultaneous substitution instead?
(define-metafunction Remora-annotated
  subst* : any [(var any) ...] -> any
  [(subst* any []) any]
  [(subst* any_orig [(var any_new) any_subs ...])
   (subst* (substitute any_orig var any_new) [any_subs ...])])
;;; Substitution for type-annotated variables
(define-metafunction Remora-annotated
  subst:t : AE:t var any -> AE:t
  [(subst:t base-val _ _) base-val]
  [(subst:t op _ _) op]
  [(subst:t (λ [var_l ...] expr:t : type) var any)
   (λ [var_l ...] (subst:t expr:t var any) : type)]
  [(subst:t (tλ [var_l ...] expr:t : type) var any)
   (tλ [var_l ...] (subst:t expr:t var any) : type)]
  [(subst:t (iλ [var_l ...] expr:t : type) var any)
   (iλ [var_l ...] (subst:t expr:t var any) : type)]
  [(subst:t (box idx ... expr:t : type) var any)
   (box idx ... (subst expr:t var any) : type)]
  [(subst:t (var : type) var any) any]
  [(subst:t var:t var_other any) var:t]
  [(subst:t (array {natural ...} [atom:t ...] : type) var any)
   (array {natural ...} [(subst:t atom:t var any) ...] : type)]
  [(subst:t (frame {natural ...} [expr:t ...] : type) var any)
   (frame {natural ...} [(subst:t expr:t var any) ...] : type)]
  [(subst:t (expr:t_fn expr:t_arg ... : type) var any)
   ((subst:t expr:t_fn var any) (subst:t expr:t_arg var any) ... : type)]
  [(subst:t (t-app expr:t type_arg ... : type_annot) var any)
   (t-app (subst:t expr:t var any) type_arg ... : type_annot)]
  [(subst:t (i-app expr:t idx ... : type) var any)
   (i-app (subst:t expr:t var any) idx ... : type)]
  [(subst:t (unbox (var_i ... var_e expr:t_box) expr:t_body : type) var any)
   (unbox (var_i ... var_e (subst:t expr:t_box var any))
     (subst:t expr:t_body var any) : type)])
(define-metafunction Remora-annotated
  subst:t* : AE:t [(var any) ...] -> AE:t
  [(subst:t* AE:t []) AE:t]
  [(subst:t* AE:t [(var any_new) any_subs ...])
   (subst:t* (subst:t AE:t var any_new) [any_subs ...])])

;;; Metafunction wrappers for type-of judgment which produces fully annotated
;;; version of a closed term (elaborate) or possibly open terms (elaborate/env)
(define-metafunction Remora-annotated
  elaborate-atom/env : sort-env kind-env type-env atom -> atom:t
  [(elaborate-atom/env sort-env kind-env type-env atom)
   atom:t_out
   (where (atom:t_out _ ...)
     ,(judgment-holds
       (type-of/atom sort-env kind-env type-env atom _ atom:t)
       atom:t))])
(define-metafunction Remora-annotated
  elaborate-expr/env : sort-env kind-env type-env expr -> expr:t
  [(elaborate-expr/env sort-env kind-env type-env expr)
   expr:t_out
   (where (expr:t_out _ ...)
     ,(judgment-holds
       (type-of/expr sort-env kind-env type-env expr _ expr:t)
       expr:t))])
(define-metafunction Remora-annotated
  elaborate/env : sort-env kind-env type-env AE -> AE:t
  [(elaborate/env any ... atom) (elaborate-atom/env any ... atom)]
  [(elaborate/env any ... expr) (elaborate-expr/env any ... expr)])
(define-metafunction Remora-annotated
  elaborate-atom : atom -> atom:t
  [(elaborate-atom atom) (elaborate-atom/env () () () atom)])
(define-metafunction Remora-annotated
  elaborate-expr : expr -> expr:t
  [(elaborate-expr expr) (elaborate-expr/env () () () expr)])
(define-metafunction Remora-annotated
  elaborate : AE -> AE:t
  [(elaborate atom) (elaborate-atom atom)]
  [(elaborate expr) (elaborate-expr expr)])


;;; Convert fully annotated term to minimally annotated form
(define-metafunction Remora-annotated
  unelaborate : AE:t -> AE
  [(unelaborate base-val) base-val]
  [(unelaborate op) op]
  [(unelaborate (var : type)) var]
  [(unelaborate (λ [var ...] expr:t : (-> [type_in ...] _)))
   (λ [(var type_in) ...] (unelaborate expr:t))]
  [(unelaborate (tλ [var ...] expr:t : (∀ [(_ kind) ...] _)))
   (tλ [(var kind) ...] (unelaborate expr:t))]
  [(unelaborate (iλ [var ...] expr:t : (Π [(_ sort) ...] _)))
   (iλ [(var sort) ...] (unelaborate expr:t))]
  [(unelaborate (array {natural_0 ... 0 natural_1 ...} _ : (Array type _)))
   (array type {natural_0 ... 0 natural_1 ...})]
  [(unelaborate (array {natural ...} [atom:t ...] : type))
   (array {natural ...} [(unelaborate atom:t) ...])]
  [(unelaborate (frame {natural_0 ... 0 natural_1 ...} _
                       : (Array type idx)))
   (frame {natural_0 ... 0 natural_1 ...}
          (Array type (drop-prefix {Shp natural_0 ... 0 natural_1 ...} idx)))]
  [(unelaborate (frame {natural ...} [expr:t ...] : (Array type _)))
   (frame {natural ...} [(unelaborate expr:t) ...])]
  [(unelaborate (expr:t_f expr:t_a ... : type))
   ((unelaborate expr:t_f) (unelaborate expr:t_a) ...)]
  [(unelaborate (t-app expr:t type ... : _))
   (t-app (unelaborate expr:t) type ...)]
  [(unelaborate (i-app expr:t idx ... : _))
   (i-app (unelaborate expr:t) idx ...)]
  [(unelaborate (Box idx ... expr:t : type))
   (box idx ... expr:t type)]
  [(unelaborate (unbox (var_i ... var_e expr:t_box) expr:t_body : type))
   (unbox (var_i ... var_e (unelaborate expr:t_box))
     (unelaborate expr:t_body))])

;;; Pass expected shape and actual shape. This metafunction assumes the indices
;;; passed in are well-formed Shapes. Returns the frame shape if it exists.
;;; Otherwise, return false.
(define-metafunction Remora-explicit
  drop-suffix : idx idx -> idx ∪ #f
  [(drop-suffix idx_0 idx_1)
   (drop-suffix/normalized (normalize-idx idx_0) (normalize-idx idx_1))])
(define-metafunction Remora-annotated
  drop-suffix/normalized : nshp nshp -> nshp ∪ #f
  [(drop-suffix/normalized {Shp} idx) idx]
  [(drop-suffix/normalized idx idx) {Shp}]
  [(drop-suffix/normalized {Shp ndim_0 ... ndim_2 ndim_3 ...}
                           {Shp ndim_1 ... ndim_2 ndim_3 ...})
   (drop-suffix/normalized (normalize-idx {Shp ndim_0 ...})
                           (normalize-idx {Shp ndim_1 ...}))]
  [(drop-suffix/normalized {++ fshp_0 ... fshp_2 fshp_3 ...}
                           {++ fshp_1 ... fshp_2 fshp_3 ...})
   (drop-suffix/normalized (normalize-idx {++ fshp_0 ...})
                           (normalize-idx {++ fshp_1 ...}))]
  [(drop-suffix/normalized {++ fshp_0 ... {Shp ndim_0 ... ndim_2 ndim_3 ...}}
                           {++ fshp_1 ... {Shp ndim_1 ... ndim_2 ndim_3 ...}})
   (drop-suffix/normalized (normalize-idx {++ fshp_0 ... {Shp ndim_0 ...}})
                           (normalize-idx {++ fshp_1 ... {Shp ndim_1 ...}}))]
  [(drop-suffix/normalized _ _) #f])

;;; Identify which frame has the other as a prefix. Return false if neither one
;;; is prefixed by the other.
(define-metafunction Remora-explicit
  larger-frame : idx idx -> idx ∪ #f
  [(larger-frame idx_0 idx_1)
   idx_0
   (where idx_diff (drop-prefix idx_1 idx_0))]
  [(larger-frame idx_0 idx_1)
   idx_1
   (where idx_diff (drop-prefix idx_0 idx_1))]
  [(larger-frame _ _) #f])
(define-metafunction Remora-explicit
  largest-frame : [idx ...+] -> idx ∪ #f
  [(largest-frame [idx]) idx]
  [(largest-frame [idx_0 idx_1 idx_rest ...])
   (largest-frame [idx_lrg idx_rest ...])
   (where idx_lrg (larger-frame idx_0 idx_1))]
  [(largest-frame _) #f])

;;; Remove a specified prefix from a shape
(define-metafunction Remora-explicit
  drop-prefix : idx idx -> idx ∪ #f
  [(drop-prefix idx_0 idx_1)
   (drop-prefix/normalized (normalize-idx idx_0)
                           (normalize-idx idx_1))])
(define-metafunction Remora-annotated
  drop-prefix/normalized : nshp nshp -> nshp ∪ #f
  [(drop-prefix/normalized {Shp} nshp) nshp]
  [(drop-prefix/normalized idx idx) {Shp}]
  [(drop-prefix/normalized {Shp ndim_2 ndim_3 ... ndim_0 ...}
                           {Shp ndim_2 ndim_3 ... ndim_1 ...})
   (drop-prefix/normalized (normalize-idx {Shp ndim_0 ...})
                           (normalize-idx {Shp ndim_1 ...}))]
  [(drop-prefix/normalized {++ fshp_2 fshp_3 ... fshp_0 ...}
                           {++ fshp_2 fshp_3 ... fshp_1 ...})
   (drop-prefix/normalized (normalize-idx {++ fshp_0 ...})
                           (normalize-idx {++ fshp_1 ...}))]
  [(drop-prefix/normalized {++ {Shp ndim_2 ndim_3 ... ndim_0 ...} fshp_0 ...}
                           {++ {Shp ndim_2 ndim_3 ... ndim_1 ...} fshp_1 ...})
   (drop-prefix/normalized (normalize-idx {++ {Shp ndim_0 ...} fshp_0 ...})
                           (normalize-idx {++ {Shp ndim_1 ...} fshp_1 ...}))]
  [(drop-prefix/normalized _ _) #f])

;;; Reduce a type index to a canonical normal form.
(define-metafunction Remora-annotated
  normalize-idx : idx -> nidx
  [(normalize-idx natural) natural]
  [(normalize-idx var) var]
  [(normalize-idx {Shp idx ...})
   {Shp (normalize-idx idx) ...}]
  [(normalize-idx {+ idx_0 ... {+ idx_1 ...} idx_2 ...})
   (normalize-idx {+ idx_0 ... idx_1 ... idx_2 ...})]
  [(normalize-idx {+ idx_0 ... natural_0 idx_1 ... natural_1 idx_2 ...})
   (normalize-idx {+ ,(+ (term natural_0) (term natural_1))
                        idx_0 ... idx_1 ... idx_2 ...})]
  [(normalize-idx {+ idx_0 idx_1 ... natural idx_2 ...})
   (normalize-idx {+ natural idx_0 idx_1 ... idx_2 ...})]
  [(normalize-idx {+ idx}) idx]
  [(normalize-idx {+}) 0]
  [(normalize-idx {+ natural ... var ...})
   {+ natural ... var_sorted ...}
   (where {var_sorted ...}
     ,(sort (term {var ...}) symbol<?))]
  [(normalize-idx {++ idx_0 ...
                        {++ idx_1 ...}
                        idx_2 ...})
   (normalize-idx {++ idx_0 ... idx_1 ... idx_2 ...})]
  [(normalize-idx {++ idx_0 ... {Shp idx_1 ...} {Shp idx_2 ...} idx_3 ...})
   (normalize-idx {++ idx_0 ... {Shp idx_1 ... idx_2 ...} idx_3 ...})]
  [(normalize-idx {++ {Shp idx ...}}) {Shp idx ...}]
  [(normalize-idx {++}) {Shp}]
  [(normalize-idx {++ idx ...}) {++ idx ...}])

;;; Rewrite every index which appears in a type in its canonical form
(define-metafunction Remora-annotated
  normalize-indices : type -> type
  [(normalize-indices var) var]
  [(normalize-indices base-type) base-type]
  [(normalize-indices (-> [type_in ...] type_out))
   (-> [(normalize-indices type_in) ...]
       (normalize-indices type_out))]
  [(normalize-indices (∀ [(var kind) ...] type))
   (∀ [(var kind) ...] (normalize-indices type))]
  [(normalize-indices (Π [(var sort) ...] type))
   (Π [(var sort) ...] (normalize-indices type))]
  [(normalize-indices (Σ [(var sort) ...] type))
   (Σ [(var sort) ...] (normalize-indices type))]
  [(normalize-indices (Array type idx))
   (Array (normalize-indices type) (normalize-idx idx))])
