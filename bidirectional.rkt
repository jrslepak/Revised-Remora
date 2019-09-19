#lang racket

(require redex
         #;"language.rkt"
         "elab-lang.rkt"
         "inez-wrapper.rkt"
         "makanin-wrapper.rkt")

;;; Utilities for converting variable-class notation into kind/sort-tag notation
(define-metafunction Remora-elab
  sort-tag : ivar -> (e:idx e:sort)
  [(sort-tag dvar) (dvar Dim)]
  [(sort-tag svar) (dvar Shape)])
(define-metafunction Remora-elab
  kind-tag : tvar -> (e:type e:kind)
  [(kind-tag atmvar) (atmvar Atom)]
  [(kind-tag arrvar) (arrvar Array)])

(define-judgment-form Remora-elab
  #:mode (synth/atom I I I O O O O)
  #:contract (synth/atom env archive atom atmtype env archive e:atom)
  ;; TODO: syn-fn (optional)
  [(check/atom env_0 archive_0
               atom atmtype
               env_1 archive_1 e:atom)
   --- syn:annot
   (synth/atom env_0 archive_0
               (atom : atmtype) atmtype
               env_1 archive_1 e:atom)]
  [(synth/atom env archive integer Int env archive integer)
   syn:int]
  [(synth/atom env archive boolean Bool env archive boolean)
   syn:bool]
  [(synth/atom env archive op (op->Itype op) env archive op)
   syn:op])

(define-judgment-form Remora-elab
  #:mode (synth/expr I I I O O O O)
  #:contract (synth/expr env archive expr arrtype env archive e:expr)
  ;; TODO: syn-app (will need synthapp judgment)
  [(synth/expr [env-entry_0 ...] archive_0
               expr_s
               ;; TODO: subtyping to reconcile possible exvar with need for Σ
               (Σ [ivar_s ...] arrtype_s)
               [env-entry_1 ...] archive_1
               e:expr_s)
   ;; The unbox arity tells how many Σ-bound ivars to demand
   (side-condition ,(= (length (term (ivar ...)) (term (ivar_s ...)))))
   (synth/expr [env-entry_1 ...
                ivar ...
                (evar : (subst* arrtype_s [(ivar_s ivar) ...]))]
               archive_1
               expr_b
               arrtype_b
               [env-entry_n ...
                ivar ... (evar : _)
                _ ...]
               archive_2
               e:expr_b)
   --- syn:unbox
   (synth/expr [env-entry_0 ...]
               archive_0
               (unbox (ivar ... evar expr_s) expr_b)
               arrtype_b
               [env-entry_n ...]
               archive_2
               (unbox (ivar ... evar e:expr_s) e:expr_b))]
  [(check/expr env_0 archive_0 expr arrtype env_1 archive_1 e:expr)
   --- syn:annot
   (synth/expr env_0 archive_0 (expr : arrtype) arrtype env_1 archive_1 e:expr)]
  [(where (_ ... (evar arrtype) _ ...) env)
   --- syn:var
   (synth/expr env archive evar arrtype env archive evar)]
  [(synth/atoms env_0 archive_0
                (atom ...) atmtype
                env_1 archive_1 [e:atom ...])
   --- syn:array
   (synth/expr env_0 archive_0
               (array {natural ...} [atom ...])
               (Array atmtype {Shp natural ...})
               env_1 archive_1
               (array {natural ...} [e:atom ...]))]
  [(synth/exprs env_0 archive_0
                (expr ...) (Array atmtype shp)
                env_1 archive_1 [e:expr ...])
   (side-condition ,(= (apply * (term (natural ...)))
                       (length (term (expr ...)))))
   --- syn:frame
   (synth/expr env_0 archive_0
               (frame {natural ...} [expr ...])
               (Array atmtype
                      (Inormalize-idx {++ {Shp natural ...} shp}))
               env_1 archive_0
               (frame {natural ...} [e:expr ...]))])


(define-judgment-form Remora-elab
  #:mode (check/atom I I I I O O O)
  #:contract (check/atom env archive atom atmtype env archive e:atom)
  ;; TODO: chk-sub, chk-fn, chk-box
  [(synth/atom env_0 archive_0 atom atmtype env_1 archive_1 e:atom)
   --- REPLACE-WITH-SUBTYPE-RULE
   (check/atom env_0 archive_0 atom atmtype env_1 archive_1 e:atom)])

(define-judgment-form Remora-elab
  #:mode (check/expr I I I I O O O)
  #:contract (check/expr env archive expr arrtype env archive e:expr)
  ;; TODO: chk-sub
  [(synth/expr env_0 archive_0 expr arrtype env_1 archive_1 e:expr)
   --- REPLACE-WITH-SUBTYPE-RULE
   (check/expr env_0 archive_0 expr arrtype env_1 archive_1 e:expr)]
  [(check/atoms env_0 archive_0 [atom ...] atmtype env_1 archive_1 [e:atom ...])
   (side-condition ,(= (apply * (term (natural ...)))
                       (length (term (atom ...)))))
   --- chk:array
   (check/expr env_0 archive_0
               (array {natural ...} [atom ...])
               (Array atmtype
                      ;; TODO: use solver query to be more permissive
                      (Shp natural ...))
               env_1 archive_1
               (array {natural ...} [e:atom ...]))])

;;;;----------------------------------------------------------------------------
;;;; Judgments related to subtyping (as instantiability)
;;;;----------------------------------------------------------------------------
;; Note: Coercing an atom doesn't necessarily work like coercing an array.
;; Consider a vector containing a polymorphic function and a monomorphic
;; function. We need that polymorphic function to become monomorphic, but the
;; only monomorphization forms in Remora are type and index application. Those
;; live in the realm of arrays, not atoms. All we can do to make an atom from
;; an atom is η expansion.
#;     [id inc]
;; must be η expanded to
#;   [(λ (y (Array Int {Shp})) (id y))
      inc]
;; which must further elaborate to
#;   [(λ (y (Array Int {Shp}))
        ((t-app (array {} [id])
                (Array Int {Shp}))
         y))
      inc]
;; For user-written λ, this maybe isn't so bad, since we'd end up with
;; something like
#;     [(λ ((x *T)) x) inc]
;; elaborating to
#;   [(λ (y (Array Int {Shp}))
        ((t-app (array {} [(tλ [*T] (λ ((x *T)) x))])
                (Array Int {Shp}))
         y))
      inc]
;; This contains a tβ redex, which should be safe to reduce at compile time
#;   [(λ (y (Array Int {Shp}))
        ((array {} [(λ ((x (Array Int {Shp}))) x)]) y))
      inc]
;; Then η reduction (which is less permissive in Remora than STLC) gives
#;   [(λ ((x (Array Int {Shp}))) x)
      inc]
;; And that's only if we were somehow directed to ascribe a polymorphic type
;; to that identity function. Without such a directive, we should type it as
;; (-> [(^ @T)] (^ @T)), with @T eventually resolving as (Array Int {Shp}). We
;; thus avoid the η round trip.
(define-judgment-form Remora-elab
  #:mode (subtype/atom I I I I O O O)
  #:contract (subtype/atom env archive atmtype atmtype env archive e:actx)
  [(subtype/atom env archive base-type base-type env archive hole)
   sub-base]
  [;; TODO: occurs check
   (instL/atom env_0 archive_0 exatmvar atmtype env_1 archive_1 e:actx)
   --- sub:instL/atom
   (subtype/atom env_0 archive_0
                 exatmvar atmtype
                 env_1 archive_1 e:actx)]
  [;; TODO: occurs check
   (instR/atom env_0 archive_0 atmtype exatmvar env_1 archive_1 e:actx)
   --- sub:instR/atom
   (subtype/atom env_0 archive_0
                 atmtype exatmvar
                 env_1 archive_1 e:actx)])
(define-judgment-form Remora-elab
  #:mode (subtype/expr I I I I O O O)
  ;; TODO: Is syntactic context too general? maybe just T-App/I-App coercions?
  #:contract (subtype/expr env archive arrtype arrtype env archive e:ectx)
  ;; TODO: Should these three (base/atmvar/arrvar) be subsumed by a refl rule?
  [(equate env_0 archive_0 shp_0 shp_1 env_1 archive_1)
   --- sub:base
   (subtype/expr
    env_0 archive_0
    (Array base-type shp_0)
    (Array base-type shp_1)
    env_1 archive_1
    hole)]
  [(equate env_0 archive_0 shp_0 shp_1 env_1 archive_1)
   --- sub:atmvar
   (subtype/expr
    env_0 archive_0
    (Array atmvar shp_0)
    (Array atmvar shp_1)
    env_1 archive_1
    hole)]
  [(subtype/expr env archive arrvar arrvar env archive hole)
   sub-arrvar]
  [(equate env_0 archive_0 shp_fl shp_fh env_1 archive_1)
   (subtype/exprs env_0 archive_0
                  [arrtype_inh ...] [arrtype_inl ...]
                  env_1 archive_1 [e:ectx_in ...])
   (subtype/expr env_1 archive_1
                 arrtype_outl arrtype_outh
                 env_2 archive_2 e:ectx_out)
   --- sub:->
   (subtype/expr env_0 archive_0
                 (Array (-> [arrtype_inl ...] arrtype_outl) shp_fl)
                 (Array (-> [arrtype_inh ...] arrtype_outh) shp_fh)
                 env_2 archive_2
                 (fn-coercion [arrtype_inl ...] [arrtype_inh ...]
                              [e:ectx_in ...] e:ectx_out))]
  [(where var_sm ,(gensym 'SM_)) ; Generate a fresh scope-marking variable
   (subtype/expr
    ;; Convert the argument type variable into an existential tvar
    [env-entry_0 ... (?i var_sm) (^ tvar) ...] archive_0
    (Array (subst* atmtype_lo [(tvar (^ tvar)) ...]) {++ shp_f shp_c})
    (Array atmtype_hi shp_hi)
    env_1 archive_1 e:ectx)
   (where [env-entry_1 ... (?i var_sm)_ ...] env_1)
   --- sub:∀L
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array (∀ [tvar ...] (Array atmtype_lo shp_c)) shp_f)
    (Array atmtype_hi shp_hi)
    [env-entry_1 ...] archive_1
    (apply-env/e:ectx env_1 (in-hole e:ectx (t-app hole (^ tvar) ...))))]
  [(where var_sm ,(gensym 'SM_)) ; Generate a fresh scope-marking variable
   (subtype/expr
    ;; Convert the argument type variable into an existential tvar
    [env-entry_0 ... (?i var_sm) (^ ivar) ...] archive_0
    (Array (subst* atmtype_lo [(ivar (^ ivar)) ...]) {++ shp_f shp_c})
    (Array atmtype_hi shp_hi)
    env_1 archive_1 e:ectx)
   (where [env-entry_1 ... (?i var_sm)_ ...] env_1)
   --- sub:ΠL
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array (Π [ivar ...] (Array atmtype_lo shp_c)) shp_f)
    (Array atmtype_hi shp_hi)
    [env-entry_1 ...] archive_1
    (apply-env/e:ectx env_1 (in-hole e:ectx (i-app hole (^ ivar) ...))))]
  ;; After destructuring the atom type as much as possible, we can conclude that
  ;; [T_1 S_1] <: [T_2 S_2] by making sure T_1 <: T_2 and S_1 ≐ S_2. The
  ;; resulting coercion will be ugly. It must apply an η-expanded version of the
  ;; atom coercion (but there doesn't seem to be much that can be done with atom
  ;; coercions because atom-level computation is so restricted).
  [(subtype/atom env_0 archive_0 atmtype_0 atmtype_1 env_1 archive_1 e:actx)
   (equate env_1 archive_1 shp_0 shp_1 env_2 archive_2)
   --- sub:Array
   (subtype/expr env_0 archive_0
                 (Array atmtype_0 shp_0)
                 (Array atmtype_1 shp_1)
                 env_2 archive_2
                 (lift-atom-coercion e:actx))])

;;; Instantiate an atom type variable on the left (i.e., as a subtype of a given
;;; goal type).
(define-judgment-form Remora-elab
  #:mode (instL/atom I I I I O O O)
  #:contract (instL/atom env archive exatmvar atmtype env archive e:actx)
  ;;----------------------------------------------------------------------------
  ;; "Structural" rules: Finalize an instantiation solution based on the state
  ;; of the environment.
  ;;----------------------------------------------------------------------------
  ;; When we have a final answer, just use it.
  [(kind-atm (env-entry_l ...) monotype)
   --- AtmL:solve
   (instL/atom (env-entry_l ... (^ tvar) env-entry_r ...) archive
             (^ tvar) monotype
             (env-entry_l ... (^ tvar monotype) env-entry_r ...) archive hole)]
  ;; If we've already instantiated this type var, make sure the old solution is
  ;; compatible with the goal type.
  [(subtype/atom [env-entry_l0 ...] archive_0
                 atmtype monotype
                 [env-entry_l0 ...] archive_1 e:actx)
   --- AtmL:solved
   (instL/atom [env-entry_l0 ... (^ tvar atmtype) env-entry_r ...] archive_0
             (^ tvar) monotype
             [env-entry_l0 ... (^ tvar atmtype) env-entry_r ...]
             archive_1 e:actx)]
  ;; If the goal is an exvar bound later, solve that exvar instead.
  [--- AtmL:reach
   (instL/atom
    [env-entry_l ... (^ tvar_lo) env-entry_m ... (^ tvar_hi) env-entry_m ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ... (^ tvar_lo) env-entry_m ... (^ tvar_hi (^ tvar_lo)) env-entry_m ...]
    archive hole)]
  ;; If the goal is an exvar bound later and already solved, propagate that
  ;; solution back to the earlier existential.
  [(kind-atm [env-entry_l ...] atmtype)
   --- AtmL:reach*
   (instL/atom
    [env-entry_l ...
     (^ tvar_lo)
     env-entry_m ...
     (^ tvar_hi atmtype)
     env-entry_m ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ...
     (^ tvar_lo atmtype)
     env-entry_m ...
     (^ tvar_hi atmtype)
     env-entry_m ...]
    archive
    hole)]
  ;;----------------------------------------------------------------------------
  ;; "De-structural" rules: Peel apart the goal type.
  ;;----------------------------------------------------------------------------
  ;; TODO: all, pi, sigma
  [(where #f (monotype? (-> [arrtype_in ...] arrtype_out)))
   (where (tvar_in ...)
     ,(map gensym (build-list (length (term [arrtype_in ...]))
                              (λ x 'arg_))))
   (where tvar_out ,(gensym 'ret_))
   (instR/arrays [env_entry_l ... (^ tvar) env_entry_r ...] archive_0
                 [arrtype_in ...]
                 [(^ tvar_in) ...]
                 env_1 archive_1 [e:ectx_in ...])
   (instL/array env_1 archive_1
                (^ tvar_out) arrtype_out
                env_2 archive_2 e:ectx_out)
   --- AtmL:fn
   (instL/atom [env_entry_l ... (^ tvar) env_entry_r ...]
               archive_0
               (^ tvar) (-> [arrtype_in ...] arrtype_out)
               [env_entry_l ...
                (^ tvar (-> [(^ tvar_in) ...] (^ tvar_out)))
                env_entry_r ...]
               archive_2
               ;; TODO: arg/ret coercion?
               hole)])

(define-judgment-form Remora-elab
  #:mode (instR/atom I I I I O O O)
  #:contract (instR/atom env archive atmtype exatmvar env archive e:actx)
  ;;----------------------------------------------------------------------------
  ;; "Structural" rules
  ;;----------------------------------------------------------------------------
  [(kind-atm (env-entry_l ...) monotype)
   --- AtmR:solve
   (instR/atom [env-entry_l ... (^ tvar) env-entry_r ...] archive
               monotype (^ tvar)
               [env-entry_l ... (^ tvar monotype) env-entry_r ...]
               archive hole)]
  [(subtype/atom [env-entry_l0 ...] archive_0
                 monotype atmtype
                 [env-entry_l1 ...] archive_1 e:actx)
   --- AtmR:solved
   (instR/atom [env-entry_l0 ... (^ tvar atmtype) env-entry_r ...] archive_0
               monotype (^ tvar)
               [env-entry_l1 ... (^ tvar atmtype) env-entry_r ...]
               archive_1 hole)]
  [--- AtmR:reach
   (instR/atom
    [env-entry_l ... (^ tvar_hi) env-entry_m ... (^ tvar_lo) env-entry_r ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ... (^ tvar_hi) env-entry_m ... (^ tvar_lo (^ tvar_hi)) env-entry_r ...]
    archive hole)]
  [(kind-atm [env-entry_l ...] atmtype)
   --- AtmR:reach*
   (instR/atom
    [env-entry_l ... (^ tvar_hi) env-entry_m ... (^ tvar_lo atmtype) env-entry_r ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ... (^ tvar_hi atmtype) env-entry_m ... (^ tvar_lo atmtype) env-entry_r ...]
    archive hole)]
  ;;----------------------------------------------------------------------------
  ;; "De-structural" rules
  ;;----------------------------------------------------------------------------
  ;; TODO: Can fn/all/pi/sigma work at all if a coercion is needed?
  #;
  [(where #f (monotype? (-> [arrtype_in ...] arrtype_out)))
   (where (tvar_in ...)
     ,(map gensym (build-list (length (term [arrtype_in ...]))
                              (λ x 'arg_))))
   (where tvar_out ,(gensym 'ret_))
   (instL/arrays [env_entry_l ... (^ tvar) env_entry_r ...] archive_0
                 [(^ tvar_in) ...]
                 [arrtype_in ...]
                 env_1 archive_1 [e:ectx_in ...])
   (instR/array env_1 archive_1
                arrtype_out (^ tvar_out)
                env_2 archive_2 e:ectx_out)
   --- AtmR:fn
   (instR/atom [env_entry_l ... (^ tvar) env_entry_r ...]
               archive_0
               (-> [arrtype_in ...] arrtype_out) (^ tvar)
               [env_entry_l ...
                (^ tvar (-> [(^ tvar_in) ...] (^ tvar_out)))
                env_entry_r ...]
               archive_2
               ;; TODO: arg/ret coercion?
               hole)]
  #;
  [(where var_sm ,(gensym 'SM_))
   ;; Maybe only allow this instantiation if the type underlying the ∀ is scalar
   (equate env_0 archive_0
           shp_lo {Shp}
           [env_entry_0 ...] archive_1)
   (instR/atom [env_entry_0 ... (?i var_sm) (^ tvar_lo) ...] archive_1
               (subst* atmtype_lo [(tvar_lo (^ tvar_lo)) ...]) (^ tvar_hi)
               [env_entry_1 ... (?i var_sm) _ ...] archive_2 e:actx)
   --- AtmR:all
   (instR/atom env_0 archive_0
               (∀ [tvar_lo ...] (Array atmtype_lo shp_lo)) (^ tvar_hi)
               [env_entry_1 ...] archive_2
               ;; TODO: instantiation coercion
               hole)])


(define-judgment-form Remora-elab
  #:mode (instL/array I I I I O O O)
  #:contract (instL/array env archive exarrvar arrtype env archive e:ectx)
  ;;----------------------------------------------------------------------------
  ;; "Structural" rules
  ;;----------------------------------------------------------------------------
  [(kind-array [env-entry_l ...] arrtype)
   --- ArrL:solve
   (instL/array [env-entry_l ... (^ tvar) env-entry_r ...] archive
                (^ tvar) arrtype
                [env-entry_l ... (^ tvar arrtype) env-entry_r ...]
                archive hole)]
  ;; TODO: solved, reach, reach*
  ;;----------------------------------------------------------------------------
  ;; "De-structural" rules
  ;;----------------------------------------------------------------------------
  [(where #f (monotype? atmtype))
   (where exatmvar (^ ,(gensym 'elt_)))
   (instL/atom [env-entry_l ...
                exatmvar (^ tvar (Array exatmvar shp))
                env-entry_r ...]
               archive_0
               exatmvar atmtype
               env_1 archive_1 e:actx)
   --- ArrL:array
   (instL/array [env-entry_l ... (^ tvar) env-entry_r ...] archive_0
                (^ tvar) (Array atmtype shp)
                env_1 archive_1
                (lift-atom-coercion e:actx))])

(define-judgment-form Remora-elab
  #:mode (instR/array I I I I O O O)
  #:contract (instR/array env archive arrtype exarrvar env archive e:ectx)
  ;;----------------------------------------------------------------------------
  ;; "Structural" rules
  ;;----------------------------------------------------------------------------
  [(kind-array [env-entry_l ...] arrtype)
   --- ArrR:solve
   (instR/array [env-entry_l ... (^ tvar) env-entry_r ...] archive
                arrtype (^ tvar)
                [env-entry_l ... (^ tvar arrtype) env-entry_r ...]
                archive hole)]
  ;; TODO: solved, reach, reach*
  ;;----------------------------------------------------------------------------
  ;; "De-structural" rules
  ;;----------------------------------------------------------------------------
  [(where #f (monotype? atmtype))
   (where exatmvar (^ ,(gensym 'elt_)))
   (instR/atom [env-entry_l ...
                (^ tvar (Array exatmvar shp)) exatmvar
                env-entry_r ...]
               archive_0
               exatmvar atmtype
               env_1 archive_1 e:actx)
   --- ArrL:array
   (instR/array [env-entry_l ... (^ tvar) env-entry_r ...] archive_0
                (Array atmtype shp) (^ tvar)
                env_1 archive_1
                (lift-atom-coercion e:actx))])


;;;;----------------------------------------------------------------------------
;;;; Type-/index-level well-formedness checks
;;;;----------------------------------------------------------------------------
(define-judgment-form Remora-elab
  #:mode (kind-atm I I)
  #:contract (kind-atm env type)
  [--- kind:Base
   (kind-atm _ base-type)]
  [(kind-array env arrtype_in) ...
   (kind-array env arrtype_out)
   --- kind:fn
   (kind-atm env (-> [arrtype_in ...] arrtype_out))]
  [(kind-array (env-entry ... tvar ...) arrtype)
   --- kind:all
   (kind-atm (env-entry ...) (∀ [tvar ...] arrtype))]
  [(kind-array (env-entry ... ivar ...) arrtype)
   --- kind:pi
   (kind-atm (env-entry ...) (Π [ivar ...] arrtype))]
  [(kind-array (env-entry ... ivar ...) arrtype)
   --- kind:sigma
   (kind-atm (env-entry ...) (Σ [ivar ...] arrtype))]
  [--- kind:atmvar
   (kind-atm [_ ... atmvar _ ...] atmvar)]
  [--- kind:exatmvar
   (kind-atm [_ ... exatmvar _ ...] exatmvar)])
(define-judgment-form Remora-elab
  #:mode (kind-array I I)
  #:contract (kind-array env type)
  [(sort-shp env shp)
   (kind-atm env atmtype)
   --- kind:Array
   (kind-array env (Array atmtype shp))]
  [--- kind:arrvar
   (kind-array [_ ... arrvar _ ...] arrvar)]
  [--- kind:exarrvar
   (kind-array [_ ... exarrvar _ ...] exarrvar)])
(define-judgment-form Remora-elab
  #:mode (sort-shp I I)
  #:contract (sort-shp env idx)
  [(sort-dim env dim) ...
   --- sort:Shp
   (sort-shp env {Shp dim ...})]
  [(sort-shp env shp) ...
   --- sort:++
   (sort-shp env {++ shp ...})]
  [--- sort:svar
   (sort-shp [_ ... svar _ ...] svar)]
  [--- sort:exsvar
   (sort-shp [_ ... exsvar _ ...] exsvar)])
(define-judgment-form Remora-elab
  #:mode (sort-dim I I)
  #:contract (sort-dim env idx)
  [(sort-dim env dim) ...
   --- sort:+
   (sort-dim env {+ dim ...})]
  [--- sort:nat
   (sort-dim env natural)]
  [--- sort:dvar
   (sort-dim [_ ... dvar _ ...] dvar)]
  [--- sort:exdvar
   (sort-dim [_ ... exdvar _ ...] exdvar)])


;;; Provide a judgment-form version of the logic used to interpret the solver's
;;; results
;;; TODO: Add "trimming" rules that match up dim* prefixes or suffixes so they
;;; don't have to be dealt with by the solver.
(define-judgment-form Remora-elab
  #:mode (equate I I I I O O)
  #:contract (equate env archive idx idx env archive)
  ;; Ask an ILP solver whether dim_0 and dim_1 can be equated and what values
  ;; must be assigned to their unsolved existential variables in order to do so.
  [(where (_ ... (env_1 archive_1) _ ...)
     (equate-shapes env_0 archive_0 shp_0 shp_1))
   --- equate:shp
   (equate env_0 archive_0 shp_0 shp_1 env_1 archive_1)]
  [--- equate:dim
   (equate env archive dim dim env archive)])
;;; Metafunction wrapper for solver call
(define-metafunction Remora-elab
  equate-shapes : env archive shp shp -> [(env archive) ...]
  [(equate-shapes env archive shp_0 shp_1)
   ,(stream->list (solutions (term env) (term archive)
                             (term shp_0) (term shp_1)))])

;;;;----------------------------------------------------------------------------
;;;; Helper judgments for typing lists of terms all at the same type
;;;;----------------------------------------------------------------------------
(define-judgment-form Remora-elab
  #:mode (synth/atoms I I I O O O O)
  #:contract (synth/atoms env archive [atom ...+] atmtype env archive [e:atom ...+])
  [(synth/atom env_0 archive_0 atom atmtype env_1 archive_1 e:atom)
   --- syn*:base
   (synth/atoms env_0 archive_0 [atom] atmtype env_1 archive_1 [e:atom])]
  [(synth/atom env_0 archive_0 atom_0 atmtype_join env_1 archive_1 e:atom_0)
   (synth/atoms env_1 archive_1 [atom_1 ...] atmtype_join env_n archive_n [e:atom_1 ...])
   ;; TODO: replace with join operation on types with exvars
   --- syn*
   (synth/atoms env_0 archive_0 [atom_0 atom_1 ...+] atmtype_join
                env_n archive_n [e:atom_0 e:atom_1 ...])])

(define-judgment-form Remora-elab
  #:mode (synth/exprs I I I O O O O)
  #:contract (synth/exprs env archive [expr ...+] arrtype env archive [e:expr ...+])
  [(synth/expr env_0 archive_0 expr arrtype env_1 archive_1 e:expr)
   --- syn*:base
   (synth/exprs env_0 archive_0 [expr] arrtype env_1 archive_1 [e:expr])]
  [(synth/expr env_0 archive_0 expr_0 arrtype_join env_1 archive_1 e:expr_0)
   (synth/exprs env_1 archive_1 [expr_1 ...] arrtype_join env_n archive_n [e:expr_1 ...])
   ;; TODO: replace with join operation on types with exvars
   --- syn*
   (synth/exprs env_0 archive_0 [expr_0 expr_1 ...+] arrtype_join
                env_n archive_n [e:expr_0 e:expr_1 ...])])

(define-judgment-form Remora-elab
  #:mode (check/atoms I I I I O O O)
  #:contract (check/atoms env archive [atom ...] atmtype env archive [e:atom ...])
  [--- chk*:base
   (check/atoms env archive [] _ env archive [])]
  [(check/atom env_0 archive_0 atom_0 atmtype env_1 archive_1 e:atom_0)
   (check/atoms env_1 archive_1 [atom_1 ...] atmtype env_n archive_n [e:atom_1 ...])
   --- chk*
   (check/atoms env_0 archive_0 [atom_0 atom_1 ...] atmtype
                env_n archive_n [e:atom_0 e:atom_1 ...])])


(define-judgment-form Remora-elab
  #:mode (check/exprs I I I I O O O)
  #:contract (check/exprs env archive [expr ...] arrtype env archive [e:expr ...])
  [--- chk*:base
   (check/exprs env archive [] _ env archive [])]
  [(check/expr env_0 archive_0 expr_0 arrtype env_1 archive_1 e:expr_0)
   (check/exprs env_1 archive_1 [expr_1 ...] arrtype env_n archive_n [e:expr_1 ...])
   --- chk*
   (check/exprs env_0 archive_0 [expr_0 expr_1 ...] arrtype
                env_n archive_n [e:expr_0 e:expr_1 ...])])

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

;;;;----------------------------------------------------------------------------
;;;; Helper judgments for instantiating lists of terms
;;;;----------------------------------------------------------------------------
(define-judgment-form Remora-elab
  #:mode (subtype/exprs I I I I O O O)
  #:contract (subtype/exprs env archive
                            [arrtype ...] [arrtype ...]
                            env archive [e:ectx ...])
  [--- subtype*:base
   (subtype/exprs env archive [] [] env archive [])]
  [(subtype/expr env_0 archive_0 arrtype_l0 arrtype_h0 env_1 archive_1 e:ectx_0)
   (subtype/exprs env_0 archive_0
                  [arrtype_l1 ...]
                  [arrtype_h1 ...]
                  env_2 archive_2 [e:ectx_1 ...])
   --- subtype*
   (subtype/exprs env_0 archive_0
                  [arrtype_l0 arrtype_l1 ...]
                  [arrtype_h0 arrtype_h1 ...]
                  env_2 archive_2 [e:ectx_0 e:ectx_1 ...])])

(define-judgment-form Remora-elab
  #:mode (instL/atoms I I I I O O O)
  #:contract (instL/atoms env archive
                          [(^ atmvar) ...] [atmtype ...]
                          env archive [e:actx ...])
  [--- atmL*:base
   (instL/atoms env archive [] [] env archive [])]
  [(instL/atom env_0 archive_0 (^ atmvar_0) atmtype_0 env_1 archive_1 e:actx_0)
   (instL/atoms env_1 archive_1
                [(^ atmvar_1) ...]
                [atmtype_1 ...]
                env_2 archive_2 [e:actx_1 ...])
   --- atmL*
   (instL/atoms env_0 archive_0
                [(^ atmvar_0) (^ atmvar_1) ...]
                [atmtype_0 atmtype_1 ...]
                env_2 archive_2 [e:actx_0 e:actx_1 ...])])
(define-judgment-form Remora-elab
  #:mode (instL/arrays I I I I O O O)
  #:contract (instL/arrays env archive
                          [(^ arrvar) ...] [arrtype ...]
                          env archive [e:ectx ...])
  [--- atmL*:base
   (instL/arrays env archive [] [] env archive [])]
  [(instL/array env_0 archive_0 (^ arrvar_0) arrtype_0 env_1 archive_1 e:ectx_0)
   (instL/arrays env_1 archive_1
                 [(^ arrvar_1) ...] [arrtype_1 ...]
                 env_2 archive_2 [e:ectx_1 ...])
   --- atmL*
   (instL/arrays env_0 archive_0
                 [(^ arrvar_0) (^ arrvar_1) ...] [arrtype_0 arrtype_1 ...]
                 env_2 archive_2 [e:ectx_0 e:ectx_1 ...])])

(define-judgment-form Remora-elab
  #:mode (instR/atoms I I I I O O O)
  #:contract (instR/atoms env archive
                          [atmtype ...] [(^ atmvar) ...]
                          env archive [e:actx ...])
  [--- atmL*:base
   (instR/atoms env archive [] [] env archive [])]
  [(instR/atom env_0 archive_0 (^ atmvar_0) atmtype_0 env_1 archive_1 e:actx_0)
   (instR/atoms env_1 archive_1
                [atmtype_1 ...] [(^ atmvar_1) ...]
                env_2 archive_2 [e:actx_1 ...])
   --- atmL*
   (instR/atoms env_0 archive_0
                [atmtype_0 atmtype_1 ...] [(^ atmvar_0) (^ atmvar_1) ...]
                env_2 archive_2 [e:actx_0 e:actx_1 ...])])
(define-judgment-form Remora-elab
  #:mode (instR/arrays I I I I O O O)
  #:contract (instR/arrays env archive
                          [(^ arrvar) ...] [arrtype ...]
                          env archive [e:ectx ...])
  [--- atmL*:base
   (instR/arrays env archive [] [] env archive [])]
  [(instR/array env_0 archive_0 (^ arrvar_0) arrtype_0 env_1 archive_1 e:ectx_0)
   (instR/arrays env_1 archive_1
                 [arrtype_1 ...] [(^ arrvar_1) ...]
                 env_2 archive_2 [e:ectx_1 ...])
   --- atmL*
   (instR/arrays env_0 archive_0
                 [arrtype_0 arrtype_1 ...] [(^ arrvar_0) (^ arrvar_1) ...]
                 env_2 archive_2 [e:ectx_0 e:ectx_1 ...])])

;;; Simple pattern-check, for where we need to ensure that a match has *failed*.
(define-metafunction Remora-elab
  monotype? : any -> boolean
  [(monotype? monotype) #t]
  [(monotype? _) #f])

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
   (array any [(apply-env/e:expr e:expr) ...])]
  [(apply-env/e:expr env (frame any e:type))
   (array any (apply-env/e:type e:type))]
  [(apply-env/e:expr env (e:expr_f e:expr_a ...))
   ((apply-env/e:expr env e:expr_f) (apply-env/e:expr env e:expr_a) ...)]
  [(apply-env/e:expr env (t-app e:expr e:type ...))
   (t-app (apply-env/e:expr env e:expr) (apply-env/e:type env e:type) ...)]
  [(apply-env/e:expr env (i-app e:expr e:idx ...))
   (i-app (apply-env/e:expr env e:expr) (apply-env/e:idx env e:idx) ...)]
  [(apply-env/e:expr env (unbox (var ... e:expr) e:expr))
   (unbox (var ... (apply-env/e:expr e:expr)) (apply-env/e:expr e:expr))])

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
  [(elab-type var) var])

(define-metafunction Remora-elab
  tvar->bind : tvar -> (e:var e:kind)
  [(tvar->bind atmvar) (atmvar Atom)]
  [(tvar->bind arrvar) (arrvar Array)])

(define-metafunction Remora-elab
  ivar->bind : ivar -> (e:var e:sort)
  [(ivar->bind dvar) (dvar Dim)]
  [(ivar->bind svar) (svar Shape)])
