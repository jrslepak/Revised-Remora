#lang racket

(require redex
         "implicit-lang.rkt"
         (except-in "language.rkt" Scl scl))

(provide Remora-explicit*
         Remora-implicit*
         op->Itype
         Remora-elab
         monotype?
         scl Scl DT DR DS
         Inormalize-idx Inormalize-type
         elab-type
         ivar->bind tvar->bind
         dim-tag shp-tag atm-tag arr-tag
         sort-tag kind-tag
         apply-env/e:expr apply-env/e:ectx
         apply-env/e:atom apply-env/e:actx
         apply-env/e:type apply-env/e:idx
         apply-env/type
         subst*
         lift-atom-coercion fn-coercion coerce-each
         arg-env-entries refine-array-type
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
  (positive-integer (side-condition (name n natural) (> (term n) 0)))
  (dim .... exdvar
       ;;; Trying this version of "more permissive environment"
       {- idx idx} {* natural idx} {/ idx positive-integer})
  (adim .... exdvar)
  (exsvar (^ svar))
  (shp .... exsvar)
  (fshp .... exsvar)
  ;; Syntactic sugar for types
  (stype (^ tvar) tvar base-type
         (-> [stype ...] stype)
         (∀ [tvar ...] stype)
         (Π [ivar ...] stype)
         (Σ [ivar ...] stype)
         [atmtype sidx ...])
  (sidx (^ ivar) ivar natural {+ dim ...}
        {Shp dim ...} {++ sidx ...}))
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

(define-metafunction Remora-implicit*
  DT : stype -> atmtype
  [(DT atmvar) atmvar]
  [(DT exatmvar) exatmvar]
  [(DT base-type) base-type]
  [(DT (-> [stype_in ...] stype_out)) (-> [(DR stype_in) ...] (DR stype_out))]
  [(DT (∀ [tvar ...] stype)) (∀ [tvar ...] (DR stype))]
  [(DT (Π [ivar ...] stype)) (Π [ivar ...] (DR stype))]
  [(DT (Σ [ivar ...] stype)) (Σ [ivar ...] (DR stype))])
(define-metafunction Remora-implicit*
  DR : stype -> arrtype
  [(DR arrvar) arrvar]
  [(DR exarrvar) exarrvar]
  [(DR [stype sidx ...]) (Array (DT stype) (Inormalize-idx {++ (DS sidx) ...}))]
  [(DR stype) (Array (DT stype) {Shp})])
(define-metafunction Remora-implicit*
  DS : sidx -> shp
  [(DS svar) svar]
  [(DS exsvar) exsvar]
  [(DS {++ sidx ...}) {++ (DS sidx) ...}]
  [(DS sidx) {Shp sidx}])

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
  [(Inormalize-idx {++ shp_0 ... {Shp} shp_1 ...})
   (Inormalize-idx {++ shp_0 ... shp_1 ...})]
  [(Inormalize-idx {++ shp_0 ... {++ shp_1 ...} shp_2 ...})
   (Inormalize-idx {++ shp_0 ... shp_1 ... shp_2 ...})]
  [(Inormalize-idx {++ shp_0 ... {Shp dim_0 ...} {Shp dim_1 ...} shp_1 ...})
   (Inormalize-idx {++ shp_0 ... {Shp dim_0 ... dim_1 ...} shp_1 ...})]
  [(Inormalize-idx {++ nshp}) nshp]
  [(Inormalize-idx {++}) {Shp}]
  [(Inormalize-idx {++ dim ...}) {++ dim ...}]
  [(Inormalize-idx nidx) nidx])

;;; Normalize indices appearing in a type
(define-metafunction Remora-elab
  Inormalize-type : type -> type
  [(Inormalize-type var) var]
  [(Inormalize-type (^ var)) (^ var)]
  [(Inormalize-type (Array type shp)) (Array (Inormalize-type type)
                                             (Inormalize-idx shp))]
  [(Inormalize-type base-type) base-type]
  [(Inormalize-type (-> [type_in ...] type_out))
   (-> [(Inormalize-type type_in) ...] (Inormalize-type type_out))]
  [(Inormalize-type (∀ [var ...] type)) (∀ [var ...] (Inormalize-type type))]
  [(Inormalize-type (Π [var ...] type)) (Π [var ...] (Inormalize-type type))]
  [(Inormalize-type (Σ [var ...] type)) (Σ [var ...] (Inormalize-type type))])

(define-metafunction Remora-elab
  split-left-dim : nshp -> (ndim nshp) or #f
  [(split-left-dim {Shp dim_car dim_cdr ...}) (dim_car {Shp dim_cdr ...})]
  [(split-left-dim {++ {Shp} shp ...})
   (split-left-dim (Inormalize-idx {++ shp ...}))]
  [(split-left-dim {++ shp_car shp_cdr ...})
   (dim_caar {++ shp_cadr shp_cdr ...})
   (where (dim_caar shp_cadr) (split-left-dim shp_car))]
  [(split-left-dim {++ _ ...}) #f]
  [(split-left-dim svar) #f]
  [(split-left-dim exsvar) #f])
(define-metafunction Remora-elab
  split-right-dim : nshp -> (nshp ndim) or #f
  [(split-right-dim {Shp dim_rdc ... dim_rac}) ({Shp dim_rdc ...} dim_rac)]
  [(split-right-dim {++ shp ... {Shp}})
   (split-right-dim (Inormalize-idx {++ shp ...}))]
  [(split-right-dim {++ shp_rdc ... shp_rac})
   ({++ shp_rdc ... shp_rdac} dim_raac)
   (where (shp_rdac dim_raac) (split-right-dim shp_rac))]
  [(split-right-dim {++ _ ...}) #f]
  [(split-right-dim svar) #f]
  [(split-right-dim exsvar) #f])

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
(define-metafunction Remora-elab
  arr-tag : var -> arrvar
  [(arr-tag var)
   ,(string->symbol (string-append "*" (symbol->string (term var))))])

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
  [(apply-env/e:atom env (tλ [(var e:kind) ...] e:expr))
   (tλ [(var e:kind) ...] (apply-env/e:expr env e:expr))]
  [(apply-env/e:atom env (iλ [(var e:sort) ...] e:expr))
   (iλ [(var e:sort) ...] (apply-env/e:expr env e:expr))]
  [(apply-env/e:atom env (box e:idx ... e:expr e:type))
   (box (apply-env/e:idx env e:idx) ...
        (apply-env/e:expr env e:expr)
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
   (apply-env/e:type env (elab-type type))
   (where [_ ... (^ var type) _ ...] env)]
  [(apply-env/e:type _ (^ var)) (^ var)]
  [(apply-env/e:type _ base-type) base-type]
  [(apply-env/e:type env (Array e:type e:idx))
   (Array (apply-env/e:type env e:type)
          (apply-env/e:idx env e:idx))]
  [(apply-env/e:type env (-> [e:type_in ...] e:type_out))
   (-> [(apply-env/e:type env e:type_in) ...]
       (apply-env/e:type env e:type_out))]
  [(apply-env/e:type env (∀ [(var kind) ...] e:type))
   (∀ [(var kind) ...] (apply-env/e:type env e:type))]
  [(apply-env/e:type env (Π [(var sort) ...] e:type))
   (Π [(var sort) ...] (apply-env/e:type env e:type))]
  [(apply-env/e:type env (Σ [(var sort) ...] e:type))
   (Σ [(var sort) ...] (apply-env/e:type env e:type))])

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
  [(apply-env/e:idx env {- idx ...})
   {- (apply-env/e:idx env idx) ...}]
  [(apply-env/e:idx env {* idx ...})
   {* (apply-env/e:idx env idx) ...}]
  [(apply-env/e:idx env {/ idx ...})
   {/ (apply-env/e:idx env idx) ...}]
  [(apply-env/e:idx env {Shp idx ...})
   {Shp (apply-env/e:idx env idx) ...}]
  [(apply-env/e:idx env {++ idx ...})
   {++ (apply-env/e:idx env idx) ...}])

(define-metafunction Remora-elab
  apply-env/type : env type -> type
  [(apply-env/type _ var) var]
  [(apply-env/type env (^ var))
   (apply-env/type env type)
   (where [_ ... (^ var type) _ ...] env)]
  [(apply-env/type _ (^ var)) (^ var)]
  [(apply-env/type _ base-type) base-type]
  [(apply-env/type env (Array type e:idx))
   (Array (apply-env/type env type)
          (apply-env/e:idx env e:idx))]
  [(apply-env/type env (-> [type_in ...] type_out))
   (-> [(apply-env/type env type_in) ...]
       (apply-env/type env type_out))]
  [(apply-env/type env (∀ [var ...] type))
   (∀ [var ...] (apply-env/type env type))]
  [(apply-env/type env (Π [var ...] type))
   (Π [var ...] (apply-env/type env type))]
  [(apply-env/type env (Σ [var ...] type))
   (Σ [var ...] (apply-env/type env type))])

(define-metafunction Remora-elab
  apply-env/env-entry : env env-entry -> env-entry
  [(apply-env/env-entry env (^ var)) (^ var)]
  [(apply-env/env-entry env var) var]
  [(apply-env/env-entry env (?i var)) (?i var)]
  [(apply-env/env-entry env (evar type))
   (evar (apply-env/type env type))]
  [(apply-env/env-entry env (^ ivar idx))
   (^ ivar (apply-env/e:idx env idx))]
  [(apply-env/env-entry env (^ tvar type))
   (^ tvar (apply-env/e:type env type))])

(define-metafunction Remora-elab
  env-propagation : env -> env
  [(env-propagation [env-entry_0 ... env-entry_1])
   [env-entry_new ... (apply-env/env-entry env-entry_1)]
   (where [env-entry_new ...]
     (env-propagation [env-entry_0 ...]))])


;;;;----------------------------------------------------------------------------
;;;; Coercion-constructing metafunctions
;;;;----------------------------------------------------------------------------
;;; Lift an atom coercion to an array coercion that performs the atom coercion
;;; on each atom in the array.
(define-metafunction Remora-elab
  lift-atom-coercion : atmtype e:actx -> e:ectx
  [(lift-atom-coercion _ hole) hole]
  [(lift-atom-coercion atmtype e:actx)
   ((scl (λ [(coerce (Scl atmtype))]
           (scl (in-hole e:actx coerce))))
    hole)])

;;; Construct a function coercion from the input and output coercions
(define-metafunction Remora-elab
  fn-coercion : [arrtype ...] [arrtype ...] arrtype [e:ectx ...] e:ectx -> e:actx
  [(fn-coercion _ _ _ [hole ...] hole) hole]
  [(fn-coercion [arrtype_inl ...] [arrtype_inh ...] arrtype_outl
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
   [(^ arrvar) (var (^ arrvar))]
   (where arrvar (arr-tag var))]
  [(arg-env-entries (var natural))
   [(^ atmvar) (^ dvar) ... (var (Array (^ atmvar) {Shp (^ dvar) ...}))]
   (where [dvar ...]
     ,(build-list (term natural) (λ (n) (term (dim-tag var ,n)))))
   (where atmvar (atm-tag var))])

;;; Make sure that an array type is split into its atom type and shape so that
;;; they can be referred to individually (this will still fail for a universal
;;; type variable).
(define-metafunction Remora-elab
  refine-array-type : env arrtype -> (env arrtype)
  [(refine-array-type env arrtype)
   (refine-array-type* env (apply-env/type env arrtype))])
(define-metafunction Remora-elab
  refine-array-type* : env arrtype -> (env arrtype)
  [(refine-array-type* [env-entry_l ... (^ arrvar) env-entry_r ...] (^ arrvar))
   ([env-entry_l ...
     (^ atmvar) (^ svar) (^ arrvar (Array (^ atmvar) (^ svar)))
     env-entry_r ...]
    (Array (^ atmvar) (^ svar)))
   (where svar ,(gensym '@RFN))
   (where atmvar ,(gensym '&RFN))]
  [(refine-array-type* env arrtype) (env arrtype)])
