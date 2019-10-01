#lang racket

(require redex
         "implicit-lang.rkt"
         "language.rkt")

(provide Remora-explicit*
         Remora-implicit*
         Remora-elab
         monotype?
         scl Scl
         Inormalize-idx
         elab-type
         ivar->bind tvar->bind
         dim-tag shp-tag atm-tag
         sort-tag kind-tag
         apply-env/e:expr apply-env/e:ectx
         apply-env/e:atom apply-env/e:actx
         apply-env/e:type apply-env/e:idx
         subst*
         lift-atom-coercion fn-coercion coerce-each
         arg-env-entries
         uses-exsvar?)

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

;;; Simple pattern-check, for where we need to ensure that a match has *failed*.
(define-metafunction Remora-elab
  monotype? : any -> boolean
  [(monotype? monotype) #t]
  [(monotype? _) #f])

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
  uses-exsvar? : shp -> boolean
  [(uses-exsvar? exsvar) #t]
  [(uses-exsvar? svar) #f]
  [(uses-exsvar? {Shp _ ...}) #f]
  [(uses-exsvar? {++ shp ...})
   ,(for/or ([s (term (shp ...))])
            (term (uses-exsvar? ,s)))])

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

;;;;----------------------------------------------------------------------------
;;;; Utility metafunctions for converting implicit-language types into
;;;; explicit-language types
;;;;----------------------------------------------------------------------------
(define-metafunction Remora-elab
  elab-type : type -> e:type
  [(elab-type (∀ (tvar ...) type))
   (∀ [(tvar->bind tvar) ...] (elab-type type))]
  [(elab-type (Π (ivar ...) type))
   (Π [(ivar->bind ivar) ...] (elab-type type))]
  [(elab-type (Σ (ivar ...) type))
   (Σ [(ivar->bind ivar) ...] (elab-type type))]
  [(elab-type (-> [type_in ...] type_out))
   (-> [(elab-type type_in) ...] (elab-type type_out))]
  [(elab-type (Array type idx))
   (Array (elab-type type) idx)]
  [(elab-type base-type) base-type]
  [(elab-type var) var]
  [(elab-type (^ var)) (^ var)])

(define-metafunction Remora-elab
  tvar->bind : tvar -> (e:var e:kind)
  [(tvar->bind atmvar) (atmvar Atom)]
  [(tvar->bind arrvar) (arrvar Array)])

(define-metafunction Remora-elab
  ivar->bind : ivar -> (e:var e:sort)
  [(ivar->bind dvar) (dvar Dim)]
  [(ivar->bind svar) (svar Shape)])


;;;;----------------------------------------------------------------------------
;;;; Utility metafunctions for generating variable names visibly associated
;;;; with some existing term-level variable
;;;;----------------------------------------------------------------------------
(define-metafunction Remora-elab
  dim-tag : var natural -> dvar
  [(dim-tag var natural)
   ,(string->symbol (string-append
                     "$"
                     (symbol->string (term var))
                     (number->string (term natural))))])
(define-metafunction Remora-elab
  shp-tag : var -> svar
  [(shp-tag var)
   ,(string->symbol (string-append "@" (symbol->string (term var))))])
(define-metafunction Remora-elab
  atm-tag : var -> atmvar
  [(atm-tag var)
   ,(string->symbol (string-append "&" (symbol->string (term var))))])

;;; Utilities for converting variable-class notation into kind/sort-tag notation
(define-metafunction Remora-elab
  sort-tag : ivar -> (e:idx e:sort)
  [(sort-tag dvar) (dvar Dim)]
  [(sort-tag svar) (dvar Shape)])
(define-metafunction Remora-elab
  kind-tag : tvar -> (e:type e:kind)
  [(kind-tag atmvar) (atmvar Atom)]
  [(kind-tag arrvar) (arrvar Array)])


;;;;----------------------------------------------------------------------------
;;;; Utility metafunctions for multiple substitution
;;;;----------------------------------------------------------------------------
(define-metafunction Remora-elab
  subst* : any [(var any) ...] -> any
  [(subst* any []) any]
  [(subst* any_orig [(var any_new) any_subs ...])
   (subst* (substitute any_orig var any_new) [any_subs ...])])

(define-metafunction Remora-elab
  apply-env/e:expr : env e:expr -> e:expr
  [(apply-env/e:expr _ var) var]
  [(apply-env/e:expr env (array any [e:atom ...]))
   (array any [(apply-env/e:atom env e:atom) ...])]
  [(apply-env/e:expr env (array any e:type))
   (array any (apply-env/e:type e:type))]
  [(apply-env/e:expr env (frame any [e:expr ...]))
   (frame any [(apply-env/e:expr env e:expr) ...])]
  [(apply-env/e:expr env (frame any e:type))
   (array any (apply-env/e:type e:type))]
  [(apply-env/e:expr env (e:expr_f e:expr_a ...))
   ((apply-env/e:expr env e:expr_f) (apply-env/e:expr env e:expr_a) ...)]
  [(apply-env/e:expr env (t-app e:expr e:type ...))
   (t-app (apply-env/e:expr env e:expr) (apply-env/e:type env e:type) ...)]
  [(apply-env/e:expr env (i-app e:expr e:idx ...))
   (i-app (apply-env/e:expr env e:expr) (apply-env/e:idx env e:idx) ...)]
  [(apply-env/e:expr env (unbox (var ... e:expr) e:expr))
   (unbox (var ... (apply-env/e:expr env e:expr)) (apply-env/e:expr env e:expr))])

(define-metafunction Remora-elab
  apply-env/e:ectx : env e:ectx -> e:ectx
  [(apply-env/e:ectx _ hole) hole]
  [(apply-env/e:ectx env (array any [e:atom_0 ... e:actx e:atom_1 ...]))
   (array any [(apply-env/e:atom env e:atom_0) ...
               (apply-env/e:actx env e:actx)
               (apply-env/e:atom env e:atom_1) ...])]
  [(apply-env/e:ectx env (frame any [e:expr_0 ... e:ectx e:expr_1 ...]))
   (array any [(apply-env/e:expr env e:expr_0) ...
               (apply-env/e:ectx env e:ectx)
               (apply-env/e:expr env e:expr_1) ...])]
  [(apply-env/e:ectx env (e:expr_0 ... e:ectx e:expr_1 ...))
   ((apply-env/e:expr env e:expr_0) ...
    (apply-env/e:ectx env e:ectx)
    (apply-env/e:expr env e:expr_1) ...)]
  [(apply-env/e:ectx env (t-app e:ectx e:type ...))
   (t-app (apply-env/e:ectx env e:ectx)
          (apply-env/e:type env e:type) ...)]
  [(apply-env/e:ectx env (i-app e:ectx e:idx ...))
   (i-app (apply-env/e:ectx env e:ectx)
          (apply-env/e:idx env e:idx) ...)]
  [(apply-env/e:ectx env (unbox (var ... e:ectx) e:expr))
   (unbox (var ... (apply-env/e:ectx env e:ectx))
     (apply-env/e:expr env e:expr))]
  [(apply-env/e:ectx env (unbox (var ... e:expr) e:ectx))
   (unbox (var ... (apply-env/e:expr env e:expr))
     (apply-env/e:ectx env e:ectx))])

(define-metafunction Remora-elab
  apply-env/e:atom : env e:atom -> e:atom
  [(apply-env/e:atom _ base-val) base-val]
  [(apply-env/e:atom _ op) op]
  [(apply-env/e:atom env (λ [(var e:type) ...] e:expr))
   (λ [(var (apply-env/e:type env e:type)) ...] (apply-env/e:expr env e:expr))]
  [(apply-env/e:atom env (Tλ [(var e:kind) ...] e:expr))
   (λ [(var e:kind) ...] (apply-env/e:expr env e:expr))]
  [(apply-env/e:atom env (Iλ [(var e:sort) ...] e:expr))
   (λ [(var e:sort) ...] (apply-env/e:expr env e:expr))]
  [(apply-env/e:atom env (box e:idx ... e:expr e:type))
   (box (apply-env/e:idx env e:idx) ...
        (apply-env/e:atom env e:expr)
        (apply-env/e:type env e:type))])

(define-metafunction Remora-elab
  apply-env/e:actx : env e:actx -> e:actx
  [(apply-env/e:actx _ hole) hole]
  [(apply-env/e:actx env (λ [(var e:type) ...] e:ectx))
   (λ [(var (apply-env/e:type env e:type)) ...] (apply-env/e:ectx env e:ectx))]
  [(apply-env/e:actx env (tλ [(var kind) ...] e:ectx))
   (tλ [(var kind) ...] (apply-env/e:ectx env e:ectx))]
  [(apply-env/e:actx env (iλ [(var sort) ...] e:ectx))
   (iλ [(var sort) ...] (apply-env/e:ectx env e:ectx))]
  [(apply-env/e:actx env (box e:idx ... e:ectx e:type))
   (box (apply-env/e:idx env e:idx) ...
        (apply-env/e:actx env e:ectx)
        (apply-env/e:type env e:type))])

(define-metafunction Remora-elab
  apply-env/e:type : env e:type -> e:type
  [(apply-env/e:type _ var) var]
  [(apply-env/e:type env (^ var))
   (apply-env/e:type env type)
   (where [_ ... (^ var type) _ ...] env)]
  [(apply-env/e:type _ (^ var)) (^ var)]
  [(apply-env/e:type _ base-type) base-type]
  [(apply-env/e:type env (Array e:type e:idx))
   (Array (apply-env/e:type env e:type)
          (apply-env/e:idx env e:idx))]
  [(apply-env/e:type env (-> [type_in ...] type_out))
   (-> [(apply-env/e:type env type_in) ...]
       (apply-env/e:type env type_out))]
  [(apply-env/e:type env (∀ [(var kind) ...] type))
   (∀ [(var kind) ...] (apply-env/e:type env type))]
  [(apply-env/e:type env (Π [(var sort) ...] type))
   (Π [(var sort) ...] (apply-env/e:type env type))]
  [(apply-env/e:type env (Σ [(var sort) ...] type))
   (Σ [(var sort) ...] (apply-env/e:type env type))])

(define-metafunction Remora-elab
  apply-env/e:idx : env e:idx -> e:idx
  [(apply-env/e:idx _ var) var]
  [(apply-env/e:idx env (^ var))
   (apply-env/e:idx env idx)
   (where [_ ... (^ var idx) _ ...] env)]
  [(apply-env/e:idx _ (^ var)) (^ var)]
  [(apply-env/e:idx _ natural) natural]
  [(apply-env/e:idx env {+ idx ...})
   {+ (apply-env/e:idx env idx) ...}]
  [(apply-env/e:idx env {Shp idx ...})
   {Shp (apply-env/e:idx env idx) ...}]
  [(apply-env/e:idx env {++ idx ...})
   {++ (apply-env/e:idx env idx) ...}])


;;;;----------------------------------------------------------------------------
;;;; Coercion-constructing metafunctions
;;;;----------------------------------------------------------------------------
;;; Lift an atom coercion to an array coercion that performs the atom coercion
;;; on each atom in the array.
(define-metafunction Remora-elab
  lift-atom-coercion : e:actx -> e:ectx
  [(lift-atom-coercion hole) hole]
  [(lift-atom-coercion e:actx) ((scl (λ [(coerce (Scl atmtype))]
                                       (in-hole e:actx coerce)))
                                hole)])

;;; Construct a function coercion from the input and output coercions
(define-metafunction Remora-elab
  fn-coercion : [arrtype ...] [arrtype ...] [e:ectx ...] e:ectx -> e:actx
  [(fn-coercion _ _ [hole ...] hole) hole]
  [(fn-coercion [arrtype_inl ...] [arrtype_inh ...]
                [e:ectx_in ...] e:ectx_out)
   ((array
     ()
     [(λ [(f (Array (-> [arrtype_inl ...] arrtype_outl)
                    {Shp}))]
        (array
         ()
         [(λ [(var_fresh arrtype_inh) ...]
            (in-hole
             e:ectx_out
             (f (in-hole e:ectx_in var_fresh) ...)))]))])
    hole)
   (where [var_fresh ...]
     ,(build-list (length (term (arrtype_inh ...))) (λ _ (gensym 'ARG_))))])

;;; Build a coercion which lifts the specified coercion over these cells
(define-metafunction Remora-elab
  coerce-each : arrtype e:ectx -> e:ectx
  [(coerce-each arrtype e:ectx)
   ((array {} [(λ ((c arrtype)) (in-hole e:ectx c))]) hole)])



;;; Generate the new environment entries associated with a λ's argument name
;;; and spec. If the a type spec is given, we only need a single env-entry
;;; binding the variable at that type. If we have a natural rank, generate the
;;; appropriate number of existential dimension variables and an existential
;;; atom variable. For `all' rank, generate an existential shape variable and an
;;; existential atom variable.
(define-metafunction Remora-elab
  arg-env-entries : (var spec) -> [(^ var) ... (var arrtype)]
  [(arg-env-entries (var arrtype)) [(var arrtype)]]
  [(arg-env-entries (var all))
   [(^ atmvar) (^ svar) (var (Array (^ atmvar) (^ svar)))]
   (where svar (shp-tag var))
   (where atmvar (atm-tag var))]
  [(arg-env-entries (var natural))
   [(^ atmvar) (^ dvar) ... (var (Array (^ atmvar) {Shp (^ dvar) ...}))]
   (where [dvar ...]
     ,(build-list (term natural) (λ (n) (term (dim-tag var ,n)))))
   (where atmvar (atm-tag var))])