#lang racket

(require redex)
(provide Remora-explicit
         Scl scl &-> &Π &Σ &∀ &
         op->type)

;;; TODO: Specialized forms of polymorphic primops should be treated as primops.

(define-language Remora-explicit
  (var variable-not-otherwise-mentioned)
  ;; Term-level pieces
  ;; The old atom/scalar distinction is now simplified. Old notation for a bare
  ;; atom now indicates a scalar, without having to wrap it in a degenerate
  ;; array literal.
  (atom base-val
        fn
        (tuple expr ...)
        (tλ [(var kind) ...] val)
        (iλ [(var sort) ...] val)
        (box idx ... expr type))
  (base-val integer boolean)
  (fn op (λ [(var type) ...] expr))
  (atval base-val fn (tuple val ...) (box idx ... val type))
  (expr var
        ;; Array literal: give shape and (row-major) sequence of atoms
        (array {natural ...} [atom ...])
        ;; For empty arrays, give element type instead of a list of elements.
        (array {natural ...+} type)
        ;; Nested array
        (frame {natural ...} (expr ...))
        ;; If empty, give the type the cells would have
        (frame {natural ...+} type)
        (expr expr ...)
        (t-app expr type ...)
        (i-app expr idx ...)
        (unbox (var ... var expr) expr))
  ;; "atom or expr," used for some convenience/utility metafunctions
  (AE atom expr)
  ;; Syntactic contexts
  (actx hole
        (λ [(var type) ...] ectx)
        (tλ [(var kind) ...] ectx)
        (iλ [(var sort) ...] ectx)
        (box idx ... ectx type)
        (tuple expr ... ectx expr ...))
  (ectx hole
        (array {natural ...} [atom ... actx atom ...])
        (frame {natural ...} [expr ... ectx expr ...])
        (expr ... ectx expr ...)
        (t-app ectx type ...)
        (i-app ectx idx ...)
        (unbox (var ... var ectx) expr)
        (unbox (var ... var expr) ectx))
  ;; Add more primops as they are needed.
  ;; TODO: how to handle curried primops?
  (op + - * and or not > < =
      length shape reduce iota reshape)
  (val var
       (array {natural ...}
              (atom ...))
       (array {natural ...}
              type))
  ;; Type-level pieces
  (type var
        base-type
        (-> [type ...] type)
        (∀ [(var kind) ...] type)
        (Π [(var sort) ...] type)
        (Σ [(var sort) ...] type)
        (Array type idx))
  (base-type Int Bool)
  (kind Array Atom)
  ;; Index-level pieces
  ;; Delimiting indices with {} is convention, not enforced by Racket/Redex.
  (idx var
       natural
       {Shp idx ...}
       {+ idx ...}
       #;{- idx ...}
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
  (λ [(var type) ...] expr #:refers-to (shadow var ...))
  (tλ [(var kind) ...] val #:refers-to (shadow var ...))
  (iλ [(var sort) ...] val #:refers-to (shadow var ...))
  (unbox (var_i ... var_e expr) expr #:refers-to (shadow var_i ... var_e))
  (∀ [(var kind) ...] type #:refers-to (shadow var ...))
  (Π [(var sort) ...] type #:refers-to (shadow var ...))
  (Σ [(var sort) ...] type #:refers-to (shadow var ...)))

;;; Build a scalar expr from any atom
(define-metafunction Remora-explicit
  scl : atom -> expr
  [(scl atom) (array {} [atom])])
;;; Build an Array type from any Atom type by applying to the scalar Shape
(define-metafunction Remora-explicit
    Scl : type -> type
    [(Scl type) (Array type {Shp})])
;;; Utilities for inserting `scalar' calls where needed.
(define-metafunction Remora-explicit
  &-> : [type ...] type -> type
  [(&-> [type_in ...] type_out)
   (Scl (-> [(& type_in) ...] (& type_out)))])
(define-metafunction Remora-explicit
  &Π : [(var sort) ...] type -> type
  [(&Π ((var sort) ...) type)
   (Π ((var sort) ...) (& type))])
(define-metafunction Remora-explicit
  &Σ : [(var sort) ...] type -> type
  [(&Σ ((var sort) ...) type)
   (Σ ((var sort) ...) (& type))])
(define-metafunction Remora-explicit
  &∀ : [(var kind) ...] type -> type
  [(&∀ [(var kind) ...] type)
   (∀ [(var kind) ...] (& type))])
(define-metafunction Remora-explicit
  & : type -> type
  [(& (Array type idx)) (Array type idx)]
  [(& (-> [type_in ...] type_out))
   (&-> [type_in ...] type_out)]
  [(& var) (Scl var)]
  [(& base-type) (Scl base-type)]
  [(& (∀ [(var kind) ...] type))
   (Scl (&∀ [(var kind) ...] type))]
  [(& (Π any ...))
   (Scl (&Π any ...))]
  #;
  [(& (Π [(var sort) ...] type))
   (Scl (&Π [(var sort) ...] type))]
  [(& (Σ [(var sort) ...] type))
   (Scl (&Σ [(var sort) ...] type))])
;;; Prettify a type by replacing scalar array types with their element types
;;; Note: This is just for display -- the result may be ill-kinded.
(define-metafunction Remora-explicit
  elide-scalar : type -> type
  [(elide-scalar (Array type {Shp})) (elide-scalar type)]
  [(elide-scalar (Array type idx)) (Array type idx)]
  [(elide-scalar base-type) base-type]
  [(elide-scalar var) var]
  [(elide-scalar (-> [type_in ...] type_out))
   (-> [(elide-scalar type_in) ...] (elide-scalar type_out))]
  [(elide-scalar (∀ [(var kind) ...] type))
   (∀ [(var kind) ...] (elide-scalar type))]
  [(elide-scalar (Π [(var sort) ...] type))
   (Π [(var sort) ...] (elide-scalar type))]
  [(elide-scalar (Σ [(var sort) ...] type))
   (Σ [(var sort) ...] (elide-scalar type))])


;;; Look up the type of a primitive operator
(define-metafunction Remora-explicit
  op->type : op -> type
  [(op->type +) (-> [(Scl Int) (Scl Int)] (Scl Int))]
  [(op->type -) (-> [(Scl Int) (Scl Int)] (Scl Int))]
  [(op->type *) (-> [(Scl Int) (Scl Int)] (Scl Int))]
  [(op->type and) (-> [(Scl Bool) (Scl Bool)] (Scl Bool))]
  [(op->type or) (-> [(Scl Bool) (Scl Bool)] (Scl Bool))]
  [(op->type not) (-> [(Scl Bool)] (Scl Bool))]
  [(op->type <) (-> [(Scl Int) (Scl Int)] (Scl Bool))]
  [(op->type =) (-> [(Scl Int) (Scl Int)] (Scl Bool))]
  [(op->type >) (-> [(Scl Int) (Scl Int)] (Scl Bool))]
  [(op->type length) (∀ [(t Atom)]
                        (Scl
                         (Π [(l Dim) (s Shape)]
                            (Scl
                             (-> [(Array t {++ {Shp l} s})] (Scl Int))))))]
  [(op->type shape) (∀ [(t Atom)]
                       (Scl
                        (Π [(s Shape)]
                           (Scl
                            (-> [(Array t s)]
                                (Scl (Σ [(r Dim)] (Array Int {Shp r}))))))))]
  [(op->type reduce) (∀ [(t Atom)]
                         (&Π [(l Dim) (f Shape) (c Shape)]
                             (&-> [(&-> [(Array t c) (Array t c)] (Array t c))
                                   (Array t {++ f c})
                                   (Array t {++ {Shp l} f c})]
                                  (Array t {++ f c}))))]
  [(op->type iota) (Π [(r Dim)]
                      (Scl (-> [(Array Int {Shp r})]
                                  (Scl (Σ [(s Shape)] (Array Int s))))))]
  [(op->type reshape) (&∀ [(t Atom)]
                          (&Π [(r Dim) (old Shape)]
                              (&-> [(Int {Shp r}) (Array t old)]
                                   (&Σ [(new Shape)] (Array t new)))))])

