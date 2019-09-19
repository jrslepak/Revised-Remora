#lang racket

(require redex
         "implicit-lang.rkt"
         "language.rkt")

(provide Remora-explicit*
         Remora-implicit*
         Remora-elab
         scl Scl
         Inormalize-idx)

;;; Define extended versions of implicit/explicit Remora which allow unsolved
;;; existential variables.
(define-extended-language Remora-implicit* Remora-implicit
  (exatmvar (^ atmvar))
  (atmtype .... exatmvar)
  (atmmono .... exatmvar)
  (exarrvar (^ arrvar))
  (arrtype .... exarrvar)
  (arrmono .... exarrvar)
  (extvar (^ tvar))
  (exdvar (^ dvar))
  (dim .... exdvar)
  (adim .... exdvar)
  (exsvar (^ svar))
  (shp .... exsvar))
(define-extended-language Remora-explicit* Remora-explicit
  (type .... (^ var))
  (idx .... (^ var) {- idx idx} {* natural idx} {/ idx postive-integer})
  (positive-integer (side-condition (name n natural) (> (term n) 0))))
;;; We need a single language which includes implicitly typed Remora and
;;; explicitly typed Remora because a Redex judgment-form is tied to a
;;; single Redex language. For elaboration, we want input in one language
;;; and output in another.
(define-union-language Remora-elab
  Remora-implicit* (e: Remora-explicit*))

;;; Shorthand functionality, duplicated from Remora-explicit
;;; Build a scalar expr from any atom
(define-metafunction Remora-elab
  scl : atom -> expr
  [(scl atom) (array {} [atom])])
;;; Build an Array type from any Atom type by applying to the scalar Shape
(define-metafunction Remora-elab
    Scl : type -> type
    [(Scl type) (Array type {Shp})])


(define-metafunction Remora-elab
  Inormalize-idx : idx -> nidx
  [(Inormalize-idx natural) natural]
  [(Inormalize-idx ivar) ivar]
  [(Inormalize-idx {Shp dim ...})
   {Shp (Inormalize-idx dim) ...}]
  [(Inormalize-idx {+ dim_0 ... {+ dim_1 ...} dim_2 ...})
   (Inormalize-idx {+ dim_0 ... dim_1 ... dim_2 ...})]
  [(Inormalize-idx {+ dim_0 ... natural_0 dim_1 ... natural_1 dim_2 ...})
   (Inormalize-idx {+ ,(+ (term natural_0) (term natural_1))
                      dim_0 ... dim_1 ... dim_2 ...})]
  [(Inormalize-idx {+ dim_0 dim_1 ... natural dim_2 ...})
   (Inormalize-idx {+ natural dim_0 dim_1 ... dim_2 ...})]
  [(Inormalize-idx {+ dim}) dim]
  [(Inormalize-idx {+}) 0]
  [(Inormalize-idx {+ natural dvar ...})
   {+ natural dvar_sorted ...}
   (where {dvar_sorted ...}
     ,(sort (term {dvar ...}) symbol<?))]
  [(Inormalize-idx {++ shp_0 ... {++ shp_1 ...} shp_2 ...})
   (Inormalize-idx {++ shp_0 ... shp_1 ... shp_2 ...})]
  [(Inormalize-idx {++ shp_0 ... {Shp dim_0 ...} {Shp dim_1 ...} shp_1 ...})
   (Inormalize-idx {++ shp_0 ... {Shp dim_0 ... dim_1 ...} shp_1 ...})]
  [(Inormalize-idx {++ {Shp dim ...}})
   {Shp dim ...}]
  [(Inormalize-idx {++}) {Shp}]
  [(Inormalize-idx {++ dim ...}) {++ dim ...}])
