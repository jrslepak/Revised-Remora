#lang racket

(require redex)
(provide Remora-implicit
         IScl Iscl I&-> I&Π I&Σ I&∀ I&
         op->Itype
         Inormalize-idx)

(define-language Remora-implicit
  (var variable-not-otherwise-mentioned)
  (evar var #;(variable-prefix ?))
  ;; Several classes of vars, which effectively carry their kind/sort
  (dvar (variable-prefix $))
  (svar (variable-prefix @))
  (ivar dvar svar)
  (atmvar (variable-prefix &))
  (arrvar (variable-prefix *))
  (tvar atmvar arrvar)
  ;; Term level
  (atom base-val
        op
        (λ [(evar spec) ...] expr)
        (box idx ... expr)
        (atom : type))
  (base-val integer boolean)
  (expr evar
        (array {natural ...} [atom ...])
        (frame {natural ...} [expr ...])
        (expr expr ...)
        (unbox (ivar ... evar expr) expr)
        (expr : type))
  (AE atom expr)
  (spec rank type)
  (rank natural all)
  (op + - * and or not > < =
      length shape reduce iota reshape)
  ;; Type level
  (atmtype atmvar
           base-type
           (-> [arrtype ...] arrtype)
           (∀ [tvar ...] arrtype)
           (Π [ivar ...] arrtype)
           (Σ [ivar ...] arrtype))
  (arrtype arrvar
           (Array atmtype shp))
  (type atmtype arrtype)
  (base-type Int Bool)
  (kind Array Atom)
  ;; Index level
  (dim dvar natural {+ dim ...})
  (ndim adim {+ adim adim ...+})
  (adim dvar natural)
  (shp svar {Shp dim ...} {++ shp ...})
  (nshp fshp {++ fshp fshp ...+} {Shp})
  (fshp svar {Shp ndim ndim ...+})
  (idx dim shp)
  (nidx ndim nshp)
  (sort Dim Shape)
  ;; Type inference environment structure
  (env (env-entry ...))
  (env-entry (evar arrtype)
             tvar (^ tvar) (^ tvar type)
             ivar (^ ivar) (^ ivar idx))
  #:binding-forms
  (λ [(evar spec) ...] expr #:refers-to (shadow evar ...))
  (unbox (ivar ... evar expr) expr #:refers-to (shadow ivar ... evar))
  (∀ [tvar ...] type #:refers-to (shadow tvar ...))
  (Π [ivar ...] type #:refers-to (shadow ivar ...))
  (Σ [ivar ...] type #:refers-to (shadow ivar ...)))

;;; Build a scalar expr from any atom
(define-metafunction Remora-implicit
  Iscl : atom -> expr
  [(Iscl atom) (array {} [atom])])
;;; Build an Array type from any Atom type
(define-metafunction Remora-implicit
    IScl : atmtype -> arrtype
    [(IScl type) (Array type {Shp})])

;;; Utilities for inserting `scalar' calls where needed.
(define-metafunction Remora-implicit
  I&-> : [type ...] type -> type
  [(I&-> [type_in ...] type_out)
   (IScl (-> [(I& type_in) ...] (I& type_out)))])
(define-metafunction Remora-implicit
  I&Π : [ivar ...] type -> type
  [(I&Π (ivar ...) type)
   (Π (ivar ...) (I& type))])
(define-metafunction Remora-implicit
  I&Σ : [ivar ...] type -> type
  [(I&Σ (ivar ...) type)
   (Σ (ivar ...) (I& type))])
(define-metafunction Remora-implicit
  I&∀ : [tvar ...] type -> type
  [(I&∀ [tvar ...] type)
   (∀ [tvar ...] (I& type))])
(define-metafunction Remora-implicit
  I& : type -> type
  [(I& (Array type idx)) (Array type idx)]
  [(I& (-> [type_in ...] type_out))
   (I&-> [type_in ...] type_out)]
  [(I& var) (IScl var)]
  [(I& base-type) (IScl base-type)]
  [(I& (∀ [tvar ...] type))
   (IScl (I&∀ [tvar ...] type))]
  [(I& (Π any ...))
   (IScl (I&Π any ...))]
  [(I& (Σ [ivar ...] type))
   (IScl (I&Σ [ivar ...] type))])

(define-metafunction Remora-implicit
  op->Itype : op -> type
  [(op->Itype +) (-> [(IScl Int) (IScl Int)] (IScl Int))]
  [(op->Itype -) (-> [(IScl Int) (IScl Int)] (IScl Int))]
  [(op->Itype *) (-> [(IScl Int) (IScl Int)] (IScl Int))]
  [(op->Itype and) (-> [(IScl Bool) (IScl Bool)] (IScl Bool))]
  [(op->Itype or) (-> [(IScl Bool) (IScl Bool)] (IScl Bool))]
  [(op->Itype not) (-> [(IScl Bool)] (IScl Bool))]
  [(op->Itype <) (-> [(IScl Int) (IScl Int)] (IScl Bool))]
  [(op->Itype =) (-> [(IScl Int) (IScl Int)] (IScl Bool))]
  [(op->Itype >) (-> [(IScl Int) (IScl Int)] (IScl Bool))]
  [(op->Itype length) (∀ [&t]
                        (IScl
                         (Π [$l @s]
                           (IScl
                            (-> [(Array &t {++ {Shp $l} @s})] (IScl Int))))))]
  [(op->Itype shape) (∀ [&t]
                       (IScl
                        (Π [@s]
                          (IScl
                           (-> [(Array &t @s)]
                               (IScl (Σ [$r] (Array Int {Shp $r}))))))))]
  [(op->Itype reduce) (∀ [&t]
                        (IScl
                         (I&Π [$l @f @c]
                              (I&-> [(I&-> [(Array &t @c) (Array &t @c)]
                                           (Array &t @c))
                                     (Array &t {++ @f @c})
                                     (Array &t {++ {Shp $l} @f @c})]
                                    (Array &t {++ @f @c})))))]
  [(op->Itype iota) (Π [$r]
                      (IScl (-> [(Array Int {Shp $r})]
                               (IScl (Σ [@s] (Array Int @s))))))]
  [(op->Itype reshape) (∀ [&t]
                         (IScl
                          (I&Π [$r @old]
                               (I&-> [(Array Int {Shp $r}) (Array &t @old)]
                                      (I&Σ [@new] (Array &t @new))))))])

(define-metafunction Remora-implicit
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
