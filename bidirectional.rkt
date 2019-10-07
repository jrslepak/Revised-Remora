#lang racket

(require redex
         "elab-lang.rkt"
         "inez-wrapper.rkt"
         "makanin-wrapper.rkt"
         "well-formedness.rkt")

(define-judgment-form Remora-elab
  #:mode (synth/atom I I I O O O O)
  #:contract (synth/atom env archive atom atmtype env archive e:atom)
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
   syn:op]
  [(where var_sm ,(gensym 'SM_))
   (where [[env-entry_exvar ... (var arrtype_generated)] ...]
     [(arg-env-entries (var spec)) ...])
   (where [env-entry_new ...]
     ,(apply append (term [[env-entry_exvar ...] ...])))
   (synth/expr [env-entry_0 ... env-entry_new ... (?i var_sm) (var arrtype_generated) ...]
               archive_0
               expr arrtype_out
               env_1 archive_1 e:expr)
   (where [env-entry_1 ... (?i var_sm) _ ...] env_1)
   --- syn:λ
   (synth/atom [env-entry_0 ...] archive_0
               (λ [(var spec) ...] expr)
               (-> [arrtype_generated ...] arrtype_out)
               [env-entry_1 ...] archive_1
               (apply-env/e:atom
                env_1
                (λ [(var (elab-type arrtype_generated)) ...] e:expr)))])

(define-judgment-form Remora-elab
  #:mode (synth/expr I I I O O O O)
  #:contract (synth/expr env archive expr arrtype env archive e:expr)
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
               (frame {natural ...} [e:expr ...]))]
  [(synth/expr env_0 archive_0
               expr_f arrtype_f
               env_1 archive_1 e:expr_fp)
   (synth-app
    env_1 archive_1 e:expr_fp arrtype_f [expr_a ...]
    arrtype_out env_2 archive_2 e:expr_fm [e:expr_a ...])
   --- syn:app
   (synth/expr env_0 archive_0
               (expr_f expr_a ...)
               (apply-env/e:type env_2 arrtype_out)
               env_2 archive_2
               (apply-env/e:expr env_2 (e:expr_fm e:expr_a ...)))])


(define-judgment-form Remora-elab
  #:mode (check/atom I I I I O O O)
  #:contract (check/atom env archive atom atmtype env archive e:atom)
  [(synth/atom env_0 archive_0 atom atmtype_lo env_1 archive_1 e:atom)
   (subtype/atom env_1 archive_1 atmtype_lo atmtype_hi env_2 archive_2 e:actx)
   --- chk:sub/atom
   (check/atom env_0 archive_0
               atom atmtype_hi
               env_2 archive_2 (in-hole e:actx e:atom))]
  [(where var_sm ,(gensym 'SM_))
   (where [[env-entry_exvar ... (var arrtype_generated)] ...]
     [(arg-env-entries (var spec)) ...])
   (where [env-entry_new ...]
     ,(apply append (term [[env-entry_exvar ... (var arrtype_generated)] ...])))
   (subtype/exprs [env-entry_0 ... (?i var_sm) env-entry_new ...] archive_0
                  [arrtype_in ...]
                  [arrtype_generated ...]
                  env_1 archive_1 [e:ectx_in ...])
   (check/expr env_1 archive_1
               expr arrtype_out
               env_2 archive_2 e:expr)
   (where [env-entry_2 ... (?i var_sm) _ ...] env_2)
   --- chk:λ
   (check/atom [env-entry_0 ...] archive_0
               (λ [(var spec) ...] expr)
               (-> [arrtype_in ...] arrtype_out)
               [env-entry_2 ...] archive_2
               (apply-env/e:atom env_2
                (λ [(var (elab-type arrtype_generated)) ...]
                  (subst* e:expr [(var (in-hole e:ectx_in var)) ...]))))]
  [(side-condition
    ;; Head off an ugly crash due to ellipsis length mismatch
    ,(= (length (term (ivar ...))) (length (term (idx ...)))))
   (sort-compat env_0 ivar idx) ...
   (check/expr env_0 archive_0
               expr (subst* arrtype [(ivar idx) ...])
               env_1 archive_1 e:expr)
   --- chk:box
   (check/atom env_0 archive_0
               (box idx ... expr)
               (Σ [ivar ...] arrtype)
               env_1 archive_1
               (box idx ... e:expr
                    (apply-env/e:type env_1
                                      (elab-type (Σ [ivar ...] arrtype)))))]
  [(check/atom [env-entry_0 ... tvar ...] archive_0
               atom atmtype
               [env-entry_1 ... tvar ... _ ...] archive_1
               e:atom)
   --- chk:∀
   (check/atom [env-entry_0 ...] archive_0
               atom (∀ [tvar ...] (Array atmtype {Shp}))
               [env-entry_1 ...] archive_1
               (tλ [(tvar->bind tvar) ...] (array {} [e:atom])))]
  [(check/atom [env-entry_0 ... ivar ...] archive_0
               atom atmtype
               [env-entry_1 ... ivar ... _ ...] archive_1
               e:atom)
   --- chk:Π
   (check/atom [env-entry_0 ...] archive_0
               atom (Π [ivar ...] (Array atmtype {Shp}))
               [env-entry_1 ...] archive_1
               (iλ [(ivar->bind ivar) ...] (array {} [e:atom])))])


(define-judgment-form Remora-elab
  #:mode (check/expr I I I I O O O)
  #:contract (check/expr env archive expr arrtype env archive e:expr)
  [;; Prune this search path except in "last resort" cases. Checking array and
   ;; frame forms at Array type should go through the associated chk rule.
   (side-condition
    ,(or (not (or (redex-match? Remora-elab
                                [(array _ ...) (Array _ ...)]
                                (term [expr arrtype_hi]))
                  (redex-match? Remora-elab
                                [(frame _ ...) (Array _ ...)]
                                (term [expr arrtype_hi]))))
         (redex-match? Remora-elab
                       (Array (Σ _ ...) _)
                       (term arrtype_hi))))
   (synth/expr env_0 archive_0 expr arrtype_lo env_1 archive_1 e:expr)
   (subtype/expr env_1 archive_1 arrtype_lo arrtype_hi env_2 archive_2 e:ectx)
   --- chk:sub/expr
   (check/expr env_0 archive_0
               expr arrtype_hi
               env_2 archive_2 (in-hole e:ectx e:expr))]
  [(check/atoms env_0 archive_0 [atom ...] atmtype env_1 archive_1 [e:atom ...])
   (side-condition ,(= (apply * (term (natural ...)))
                       (length (term (atom ...)))))
   (equate env_1 archive_1 shp {Shp natural ...} env_2 archive_2)
   --- chk:array
   (check/expr env_0 archive_0
               (array {natural ...} [atom ...])
               (Array atmtype shp)
               env_2 archive_2
               (array {natural ...} [e:atom ...]))]
  [(where exsvar (^ ,(gensym '@CELL_)))
   (check/exprs [env-entry_0 ... exsvar] archive_0
                [expr ...] (Array atmtype exsvar)
                env_1 archive_1 [e:expr ...])
   (equate env_1 archive_1
           shp {++ {Shp natural ...} exsvar}
           env_2 archive_2)
   (side-condition ,(= (apply * (term (natural ...)))
                       (length (term (expr ...)))))
   --- chk:frame
   (check/expr [env-entry_0 ...] archive_0
               (frame {natural ...} [expr ...])
               (Array atmtype shp)
               env_2 archive_2
               (frame {natural ...} [e:expr ...]))]
  ;; Trying to add some flexibility to account for the possibility of a ∀ with a
  ;; non-scalar body. Then result cells from t-app will have nonscalar shape, so
  ;; the result shape is not necessarily the same as the frame shape.
  ;; Example (sugared) elaborated term:
  ;;  [(tλ (*t) [(λ ((x *t)) 1) (λ ((x *t)) 2)])
  ;;   (tλ (*t) [(λ ((x *t)) 3) (λ ((x *t)) 4)])]
  ;;  with type [(∀ (*t) [(-> [*t] Int) 2]) 2]
  ;; Perhaps the underlying implicit term here ought to be a frame insteaed of
  ;; an array, and only a ∀ that wraps the entire thing should work with array?
  ;; As a simplified form, allow any expression to have a ∀ wrapped around the
  ;; whole thing. In order to get a split-shape universal, the programmer will
  ;; have to write a frame of array literals.
  [(equate [env-entry_0 ... tvar ...] archive_0
           shp_scalar {Shp}
           env_1 archive_1)
   (check/expr env_1 archive_1
               expr (Array atmtype shp_c)
               [env-entry_2 ... tvar ... _ ...] archive_2
               e:expr)
   --- chk:Array∀
   (check/expr [env-entry_0 ...] archive_0
               expr
               (Array (∀ [tvar ...] (Array atmtype shp_c)) shp_scalar)
               [env-entry_2 ...] archive_2
               (array {} [(tλ [(tvar->bind tvar) ...] e:expr)]))]
  [(equate [env-entry_0 ... ivar ...] archive_0
           shp_scalar {Shp}
           env_1 archive_1)
   (check/expr env_1 archive_1
               expr (Array atmtype shp_c)
               [env-entry_2 ... ivar ... _ ...] archive_2
               e:expr)
   --- chk:ArrayΠ
   (check/expr [env-entry_0 ...] archive_0
               expr
               (Array (Π [ivar ...] (Array atmtype shp_c)) shp_scalar)
               [env-entry_2 ...] archive_2
               (array {} [(iλ [(ivar->bind ivar) ...] e:expr)]))])

(define-judgment-form Remora-elab
  #:mode (synth-app I I I I I O O O O O)
  #:contract
  (synth-app
   ;; input env, input archive
   ;; partly elaborated fn expr, fn type, arg exprs
   env archive e:expr type [expr ...]
   ;; result type, output env, output archive,
   ;; monomorphized elaborated fn expr, elaborated arg exprs
   type env archive e:expr [e:expr ...])
  [(synth-app [env-entry_0 ... (^ tvar) ...] archive_0
              e:expr_fp (subst* (Array atmtype_fun {++ shp_all shp_fun})
                                [(tvar (^ tvar)) ...])
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              e:expr_fm [e:expr_arg ...])
   --- app:∀
   (synth-app [env-entry_0 ...] archive_0
              e:expr_fp (Array (∀ [tvar ...] (Array atmtype_fun shp_fun)) shp_all)
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              (apply-env/e:expr env_1 (t-app e:expr_fm (^ tvar) ...))
              [e:expr_arg ...])]
  [(synth-app [env-entry_0 ... (^ ivar) ...] archive_0
              e:expr_fp (subst* (Array atmtype_fun {++ shp_all shp_fun})
                                [(ivar (^ ivar)) ...])
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              e:expr_fm [e:expr_arg ...])
   --- app:Π
   (synth-app [env-entry_0 ...] archive_0
              e:expr_fp (Array (Π [ivar ...] (Array atmtype_fun shp_fun)) shp_all)
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              (apply-env/e:expr env_1 (i-app e:expr_fm (^ ivar) ...))
              [e:expr_arg ...])]
  ;; Applying a monomorphic unary function array, where the function array
  ;; provides the principal frame
  [(where svar_afrm ,(gensym '@AFRM_))
   (where svar_aext ,(gensym '@AEXT_))
   (where shp_afrm
     ,(if (term (uses-exsvar? shp_in))
          (term {Shp})
          (term (^ svar_afrm))))
   (check/expr [env-entry_0 ... (^ svar_afrm) (^ svar_aext)] archive_0
               expr_arg (Array atmtype_in {++ shp_afrm shp_in})
               env_1 archive_1
               e:expr_arg)
   (equate env_1 archive_1 shp_fun {++ shp_afrm (^ svar_aext)}
           env_2 archive_2)
   ;; Imagine we have a curried function. After consuming only this first
   ;; argument, what shape does the function array have? That is the "frame
   ;; shape so far" at this point in processing the whole n-ary application.
   (synth-app env_2 archive_2
              e:expr_fun
              (Array (-> [arrtype_rest ...]
                         (Array atmtype_out shp_out))
                     shp_fun)
              [expr_rest ...]
              arrtype_out
              env_3 archive_3
              ;; At this point, there should be no more substantive changes to
              ;; the elaborated function because the ∀/Π layers have all been
              ;; removed, but giving a new metavariable allows some wiggle room
              ;; for environment-application results to provide new info.
              e:expr_fm [e:expr_rest ...])
   --- app:->*f
   (synth-app [env-entry_0 ...] archive_0
              e:expr_fun
              (Array (-> [(Array atmtype_in shp_in) arrtype_rest ...]
                         (Array atmtype_out shp_out))
                     shp_fun)
              [expr_arg expr_rest ...]
              arrtype_out
              env_3 archive_3
              e:expr_fm [e:expr_arg e:expr_rest ...])]
  ;; Applying a monomorphic unary function array, where the argument array
  ;; provides the principal frame
  [(where svar_afrm ,(gensym '@AFRM_))
   (where svar_fext ,(gensym '@FEXT_))
   (where shp_afrm
     ,(if (term (uses-exsvar? shp_in))
          (term {Shp})
          (term (^ svar_afrm))))
   (check/expr [env-entry_0 ... (^ svar_afrm) (^ svar_fext)] archive_0
               expr_arg (Array atmtype_in {++ shp_afrm shp_in})
               env_1 archive_1
               e:expr_arg)
   (equate env_1 archive_1 shp_afrm {++ (^ svar_fext) shp_fun}
           env_2 archive_2)
   (synth-app env_2 archive_2
              e:expr_fun
              (Array (-> [arrtype_rest ...]
                         (Array atmtype_out shp_out))
                     shp_afrm)
              [expr_rest ...]
              arrtype_out
              env_3 archive_3
              e:expr_fm [e:expr_rest ...])
   --- app:->*a
   (synth-app [env-entry_0 ...] archive_0
              e:expr_fun
              (Array (-> [(Array atmtype_in shp_in) arrtype_rest ...]
                         (Array atmtype_out shp_out))
                     shp_fun)
              [expr_arg expr_rest ...]
              arrtype_out
              env_3 archive_3
              e:expr_fm [e:expr_arg e:expr_rest ...])]
  [--- app:->0
   (synth-app env_0 archive_0
              e:expr_fun
              (Array (-> [] (Array atmtype_out shp_out))
                     shp_fun)
              []
              (Array atmtype_out {++ shp_fun shp_out})
              env_0 archive_0
              e:expr_fun [])])

;;;;----------------------------------------------------------------------------
;;;; Judgments related to subtyping (as instantiability)
;;;;----------------------------------------------------------------------------
(define-judgment-form Remora-elab
  #:mode (subtype/atom I I I I O O O)
  #:contract (subtype/atom env archive atmtype atmtype env archive e:actx)
  [--- sub:base
   (subtype/atom env archive base-type base-type env archive hole)]
  [--- sub:atmvar
   (subtype/atom env archive atmvar atmvar env archive hole)]
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
  ;; TODO: sub:ΣL, sub:ΣR
  #:mode (subtype/expr I I I I O O O)
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
  [--- sub:arrvar
   (subtype/expr env archive arrvar arrvar env archive hole)]
  [(equate env_0 archive_0 shp_fl shp_fh env_1 archive_1)
   (subtype/exprs env_1 archive_1
                  [arrtype_inh ...] [arrtype_inl ...]
                  env_2 archive_2 [e:ectx_in ...])
   (subtype/expr env_2 archive_2
                 arrtype_outl arrtype_outh
                 env_3 archive_3 e:ectx_out)
   --- sub:->
   (subtype/expr env_0 archive_0
                 (Array (-> [arrtype_inl ...] arrtype_outl) shp_fl)
                 (Array (-> [arrtype_inh ...] arrtype_outh) shp_fh)
                 env_3 archive_3
                 (fn-coercion [arrtype_inl ...] [arrtype_inh ...]
                              [e:ectx_in ...] e:ectx_out))]
  [(where var_sm ,(gensym 'SM_)) ; Generate a fresh scope-marking variable
   (subtype/expr
    ;; Convert the argument type variable into an existential tvar
    [env-entry_0 ... (?i var_sm) (^ tvar) ...] archive_0
    (subst* (Array atmtype_lo {++ shp_f shp_c}) [(tvar (^ tvar)) ...])
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
  [(subtype/expr
    [env-entry_0 ... tvar ...] archive_0
    (Array atmtype_lo shp_lo)
    (Array atmtype_hi {++ shp_f shp_c})
    env_1 archive_1 e:ectx)
   --- sub:∀R
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array atmtype_lo shp_lo)
    (Array (∀ [tvar ...] (Array atmtype_hi shp_c)) shp_f)
    env_1 archive_1
    ;; Each shp_c cell needs to get wrapped in the ∀ by tη expansion
    (coerce-each (Array atmtype_hi shp_c) e:ectx)
    #;
    ((array
      {}
      [(λ ((c (Array atmtype_hi shp_c)))
         (array {} [(tλ [tvar ...] c)]))])
     e:ectx))]
  [(where var_sm ,(gensym 'SM_)) ; Generate a fresh scope-marking variable
   (subtype/expr
    ;; Convert the argument type variable into an existential tvar
    [env-entry_0 ... (?i var_sm) (^ ivar) ...] archive_0
    (subst* (Array atmtype_lo {++ shp_f shp_c}) [(ivar (^ ivar)) ...])
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
  [(subtype/expr
    [env-entry_0 ... ivar ...] archive_0
    (Array atmtype_lo shp_lo)
    (Array atmtype_hi {++ shp_f shp_c})
    env_1 archive_1 e:ectx)
   --- sub:ΠR
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array atmtype_lo shp_lo)
    (Array (Π [ivar ...] (Array atmtype_hi shp_c)) shp_f)
    env_1 archive_1
    ;; Each shp_c cell needs to get wrapped in the ∀ by iη expansion
    ((array
      {}
      [(λ ((c (Array atmtype_hi shp_c)))
         (array {} [(iλ [ivar ...] c)]))])
     e:ectx))]
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
                 (lift-atom-coercion e:actx))]
  ;; Here we have something regular but need to put it in the form used by
  ;; irregular data.
  [(where var_sm ,(gensym 'SM_))
   (subtype/expr
    [env-entry_0 ... (?i var_sm) (^ ivar) ...] archive_0
    (Array atmtype_lo shp_lo)
    (subst* (Array atmtype_hi {++ shp_f shp_c}) [(ivar (^ ivar)) ...])
    env_1 archive_1 e:ectx)
   (where [env-entry_1 ... (?i var_sm)_ ...] env_1)
   --- sub:ΣR
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array atmtype_lo shp_lo)
    (Array (Σ [ivar ...] (Array atmtype_hi shp_c)) shp_f)
    [env-entry_1 ...] archive_1
    (apply-env/e:ectx env_1
                      (coerce-each
                       (subst* (Array atmtype_hi shp_c) [(ivar (^ ivar)) ...])
                       (array []
                              {(box (^ ivar) ... hole
                                    (Σ [(ivar->bind ivar) ...] (Array atmtype_hi shp_c)))}))))])

;;;;----------------------------------------------------------------------------
;;;; Subtype instantiation judgments
;;;; Note: only "structural" rules work for atom subtyping because we cannot
;;;; build a nontrivial coercion context.
;;;;----------------------------------------------------------------------------
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
    [env-entry_l ... (^ tvar_lo) env-entry_m ... (^ tvar_hi) env-entry_r ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ...
     (^ tvar_lo) env-entry_m ...
     (^ tvar_hi (^ tvar_lo)) env-entry_r ...]
    archive hole)]
  ;; If the goal is an exvar bound later and already solved, propagate that
  ;; solution back to the earlier existential.
  [(instL/atom [env-entry_l ...
                (^ tvar_lo) env-entry_m ...
                (^ tvar_hi atmtype) env-entry_r ...]
               archive_0
               (^ tvar_lo) atmtype
               env_1 archive_1 e:actx)
   --- AtmL:reach*
   (instL/atom
    [env-entry_l ...
     (^ tvar_lo) env-entry_m ...
     (^ tvar_hi atmtype) env-entry_r ...]
    archive_0
    (^ tvar_lo) (^ tvar_hi)
    env_1 archive_1 e:actx)])

(define-judgment-form Remora-elab
  #:mode (instR/atom I I I I O O O)
  #:contract (instR/atom env archive atmtype exatmvar env archive e:actx)
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
               archive_1 e:actx)]
  [--- AtmR:reach
   (instR/atom
    [env-entry_l ... (^ tvar_hi) env-entry_m ... (^ tvar_lo) env-entry_r ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ...
     (^ tvar_hi) env-entry_m ...
     (^ tvar_lo (^ tvar_hi)) env-entry_r ...]
    archive hole)]
  [(instR/atom [env-entry_l ...
                (^ tvar_hi) env-entry_m ...
                (^ tvar_lo atmtype) env-entry_r ...]
               archive_0
               atmtype (^ tvar_hi)
               env_1 archive_1 e:actx)
   --- AtmR:reach*
   (instR/atom
    [env-entry_l ...
     (^ tvar_hi) env-entry_m ...
     (^ tvar_lo atmtype) env-entry_r ...]
    archive_0
    (^ tvar_lo) (^ tvar_hi)
    env_1 archive_1 e:actx)])


(define-judgment-form Remora-elab
  #:mode (instL/array I I I I O O O)
  #:contract (instL/array env archive exarrvar arrtype env archive e:ectx)
  ;;----------------------------------------------------------------------------
  ;; "Structural" rules
  ;;----------------------------------------------------------------------------
  [(kind-array [env-entry_l ...] monotype)
   --- ArrL:solve
   (instL/array [env-entry_l ... (^ tvar) env-entry_r ...] archive
                (^ tvar) monotype
                [env-entry_l ... (^ tvar monotype) env-entry_r ...]
                archive hole)]
  [(subtype/expr [env-entry_l0 ...] archive_0
                 arrtype monotype
                 [env-entry_l1 ...] archive_1 e:ectx)
   --- ArrL:solved
   (instL/array [env-entry_l0 ... (^ tvar arrtype) env-entry_r ...] archive_0
                (^ tvar) monotype
                [env-entry_l1 ... (^ tvar arrtype) env-entry_r ...] archive_1
                e:ectx)]
  [--- ArrL:reach
   (instL/array
    [env-entry_l ... (^ tvar_lo) env-entry_m ... (^ tvar_hi) env-entry_r ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ...
     (^ tvar_lo) env-entry_m ...
     (^ tvar_hi (^ tvar_lo)) env-entry_r ...]
    archive hole)]
  [(instL/array [env-entry_l ...
                 (^ tvar_lo) env-entry_m ...
                 (^ tvar_hi arrtype) env-entry_r ...]
                archive_0
                (^ tvar_lo) arrtype
                env_1 archive_1 e:ectx)
   --- ArrL:reach*
   (instL/array
    [env-entry_l ...
     (^ tvar_lo) env-entry_m ...
     (^ tvar_hi arrtype) env-entry_r ...]
    archive_0
    (^ tvar_lo) (^ tvar_hi)
    env_1 archive_1 e:ectx)]
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
  [(kind-array [env-entry_l ...] monotype)
   --- ArrR:solve
   (instR/array [env-entry_l ... (^ tvar) env-entry_r ...] archive
                (^ tvar) monotype
                [env-entry_l ... (^ tvar monotype) env-entry_r ...]
                archive hole)]
  [(subtype/expr [env-entry_l0 ...] archive_0
                 monotype arrtype
                 [env-entry_l1 ...] archive_1 e:ectx)
   --- ArrR:solved
   (instR/array [env-entry_l0 ... (^ tvar arrtype) env-entry_r ...] archive_0
                monotype (^ tvar)
                [env-entry_l1 ... (^ tvar arrtype) env-entry_r ...] archive_1
                e:ectx)]
  [--- ArrR:reach
   (instR/array
    [env-entry_l ... (^ tvar_hi) env-entry_m ... (^ tvar_lo) env-entry_r ...]
    archive
    (^ tvar_lo) (^ tvar_hi)
    [env-entry_l ...
     (^ tvar_hi) env-entry_m ...
     (^ tvar_lo (^ tvar_hi)) env-entry_r ...]
    archive hole)]
  [(instR/array [env-entry_l ...
                 (^ tvar_hi) env-entry_m ...
                 (^ tvar_lo arrtype) env-entry_r ...]
                archive_0
                arrtype (^ tvar_hi)
                env_1 archive_1 e:ectx)
   --- ArrR:reach*
   (instR/array
    [env-entry_l ...
     (^ tvar_hi) env-entry_m ...
     (^ tvar_lo arrtype) env-entry_r ...]
    archive_0
    (^ tvar_lo) (^ tvar_hi)
    env_1 archive_1 e:ectx)]
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
     (equate-shapes env_0 archive_0
                    (apply-env/e:idx env_0 shp_0)
                    (apply-env/e:idx env_0 shp_1)))
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
   (check/atoms env_1 archive_1 [atom_1 ...] atmtype_join env_n archive_n [e:atom_1 ...])
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
   (check/exprs env_1 archive_1 [expr_1 ...] arrtype_join env_n archive_n [e:expr_1 ...])
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
   (subtype/exprs env_1 archive_1
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
