#lang racket

(require redex)
(provide Remora-explicit
         scalar &-> &Π &Σ &∀ &
         op->type)

(define-language Remora-explicit
  (var variable-not-otherwise-mentioned)
  ;; Term-level pieces
  ;; The old atom/scalar distinction is now simplified. Old notation for a bare
  ;; atom now indicates a scalar, without having to wrap it in a degenerate
  ;; array literal.
  (scal base-val
        op
        var
        (λ var type expr)
        (Tλ var val)
        (Iλ var sort val))
  (expr scal
        (Arr (expr ...)
             (natural ...+))
        ;; For empty arrays, give element type instead of a list of elements.
        (Arr type
             (natural ...+))
        (expr expr)
        (TApp expr type)
        (IApp expr idx)
        (Box idx expr type)
        (Unbox (var var expr) expr))
  (base-val integer boolean)
  ;; Add more primops as they are needed.
  (op + - * and or not > < =
      length shape reduce iota reshape)
  (val scal
       (Arr (scal ...)
            (natural ...))
       (Arr type
            (natural ...)))
  ;; Type-level pieces
  ;; Rather than a built-in, general Array type constructor, every type which is
  ;; meant to be used as an atom in arrays is now itself a type constructor. The
  ;; kind (Shape -> ★) can be seen as the kind of atom types and ★ as the kind
  ;; of array types.
  (type var
        base-type
        (type -> type)
        (∀ var type)
        (Π var sort type)
        (Σ var sort type)
        (type idx))
  (base-type Int Bool)
  (kind ★
        (sort -> kind)) ; This is more flexible than I expect to actually need.
  ;; Index-level pieces
  ;; Delimiting indices with {} is convention, not enforced by Racket/Redex.
  (idx var
       natural
       {Shp idx ...}
       {+ idx ...}
       {++ idx ...})
  (sort Dim Shape)
  ;; Environment structure
  (expr-bind (var expr))
  (expr-env (expr-bind ...))
  (idx-bind (var idx))
  (idx-env (idx-bind ...))
  (type-bind (var type))
  (type-env (type-bind ...))
  (kind-bind (var kind))
  (kind-env (kind-bind ...))
  (sort-bind (var sort))
  (sort-env (sort-bind ...))
  ;; Note: Unlike in earlier Redex models of DML-like languages, Redex's
  ;; built-in binding mechanics only allow for a single namespace.
  #:binding-forms
  (λ var type expr #:refers-to var)
  (Tλ var val #:refers-to var)
  (Iλ var sort val #:refers-to var)
  (Unbox (var_i var_e expr) expr #:refers-to (shadow var_i var_e))
  (∀ var type #:refers-to var)
  (Π var sort type #:refers-to var)
  (Σ var sort type #:refers-to var))

;;; Build a ★ type from any (Shape -> ★) type by applying to the scalar Shape
(define-metafunction Remora-explicit
    scalar : type -> type
    [(scalar type) (type (Shp))])
;;; Utilities for inserting `scalar' calls where needed.
(define-metafunction Remora-explicit
  &-> : [type ...] type -> type
  [(&-> [type_in] type_out)
   (scalar ((& type_in) -> (& type_out)))]
  [(&-> [type_0 type_1 ...] type_n)
   (& ((& type_0) -> (&-> [type_1 ...] type_n)))])
(define-metafunction Remora-explicit
  &Π : [(var sort) ...] type -> type
  [(&Π [(var sort)] type) (scalar (Π var sort (& type)))]
  [(&Π [(var_0 sort_0) (var_1 sort_1) ...] type)
   (&Π [(var_0 sort_0)] (&Π [(var_1 sort_1) ...] type))])
(define-metafunction Remora-explicit
  &Σ : [(var sort) ...] type -> type
  [(&Σ [(var sort)] type) (scalar (Σ var sort (& type)))]
  [(&Σ [(var_0 sort_0) (var_1 sort_1) ...] type)
   (&Σ [(var_0 sort_0)] (&Σ [(var_1 sort_1) ...] type))])
(define-metafunction Remora-explicit
  &∀ : [var ...] type -> type
  [(&∀ [var] type) (scalar (∀ var (& type)))]
  [(&∀ [var_0 var_1 ...] type)
   (&∀ [var_0] (&∀ [var_1 ...] type))])
(define-metafunction Remora-explicit
  & : type -> type
  [(& (type idx)) (type idx)]
  [(& (type_in -> type_out))
   (scalar ((& type_in) -> (& type_out)))]
  [(& var) (scalar var)]
  [(& base-type) (scalar base-type)]
  [(& (∀ var type))
   (scalar (∀ var (& type)))]
  [(& (Π var sort type))
   (scalar (Π var sort (& type)))]
  [(& (Σ var sort type))
   (scalar (Σ var sort (& type)))])
;;; Prettify a type by replacing scalar array types with their element types
;;; Note: This is just for display -- the result may be ill-kinded.
(define-metafunction Remora-explicit
  elide-scalar : type -> type
  [(elide-scalar (type {Shp})) (elide-scalar type)]
  [(elide-scalar (type idx)) (type idx)]
  [(elide-scalar base-type) base-type]
  [(elide-scalar var) var]
  [(elide-scalar (type_in -> type_out))
   ((elide-scalar type_in) -> (elide-scalar type_out))]
  [(elide-scalar (∀ var type)) (∀ var (elide-scalar type))]
  [(elide-scalar (Π var sort type)) (Π var sort (elide-scalar type))]
  [(elide-scalar (Σ var sort type)) (Σ var sort (elide-scalar type))])


;;; Look up the type of a primitive operator
(define-metafunction Remora-explicit
  op->type : op -> type
  [(op->type +) (&-> [Int Int] Int)]
  [(op->type -) (&-> [Int Int] Int)]
  [(op->type *) (&-> [Int Int] Int)]
  [(op->type and) (&-> [Bool Bool] Bool)]
  [(op->type or) (&-> [Bool Bool] Bool)]
  [(op->type not) (&-> [Bool] Bool)]
  [(op->type <) (&-> [Int Int] Bool)]
  [(op->type >) (&-> [Int Int] Bool)]
  [(op->type length) (&∀ [t]
                         (&Π [(l Dim) (s Shape)]
                             (&-> [(t {++ {Shp l} s})] Int)))]
  [(op->type shape) (&∀ [t]
                        (&Π [(s Shape)]
                            (&-> [(t s)]
                                 (&Σ [(r Dim)] (Int {Shp r})))))]
  [(op->type reduce) (&∀ [t]
                         (&Π [(l Dim) (f Shape) (c Shape)]
                             (&-> [(&-> [(t c) (t c)] (t c))
                                   (t {++ f c})
                                   (t {++ {Shp l} f c})]
                                  (t {++ f c}))))]
  [(op->type iota) (&Π [(r Dim)] (&-> [(Int {Shp r})]
                                      (&Σ [(s Shape)] (Int s))))]
  [(op->type reshape) (&∀ [t]
                          (&Π [(r Dim) (old Shape)]
                              (&-> [(Int {Shp r}) (t old)]
                                   (&Σ [(new Shape)] (t new)))))])

