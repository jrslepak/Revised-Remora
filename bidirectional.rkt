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
               (Inormalize-type
                (apply-env/type
                 env_1 (-> [arrtype_generated ...] arrtype_out)))
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
               (Array (Σ [ivar_s ...] arrtype_s) shp_f)
               [env-entry_1 ...] archive_1
               e:expr_s)
   ;; The unbox arity tells how many Σ-bound ivars to demand
   (side-condition ,(= (length (term (ivar ...))) (length (term (ivar_s ...)))))
   ;; Using partially-specified check should be more permissive than synth
   (where atmvar_b ,(gensym '&ub))
   (where svar_b ,(gensym '@ub))
   (where [atmtype_b shp_b] [(^ atmvar_b) (^ svar_b)])
   (check/expr [env-entry_1 ...
                (^ atmvar_b) (^ svar_b)
                ivar ...
                (evar (subst* arrtype_s [(ivar_s ivar) ...]))]
               archive_1
               expr_b
               (Array atmtype_b shp_b)
               [env-entry_n ...
                ivar ... (evar _)
                _ ...]
               archive_2
               e:expr_b)
   (kind-array [env-entry_n ...]
               (apply-env/e:type
                [env-entry_n ...]
                (elab-type (Array atmtype_b {++ shp_f shp_b}))))
   --- syn:unbox
   (synth/expr [env-entry_0 ...]
               archive_0
               (unbox (ivar ... evar expr_s) expr_b)
               (Array atmtype_b {++ shp_f shp_b})
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
                (expr ...) arrtype
                env_1 archive_1 [e:expr ...])
   (where (env_2 (Array atmtype shp)) (articulate-array-type env_1 arrtype))
   (side-condition ,(= (apply * (term (natural ...)))
                       (length (term (expr ...)))))
   --- syn:frame
   (synth/expr env_0 archive_0
               (frame {natural ...} [expr ...])
               (Array atmtype
                      (Inormalize-idx {++ {Shp natural ...} shp}))
               env_2 archive_1
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
               (apply-env/type env_2 arrtype_out)
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
               [env-entry_2 ... (?i var_sm) env-entry_3 ...]
               archive_2 e:expr)
   --- chk:λ
   (check/atom [env-entry_0 ...] archive_0
               (λ [(var spec) ...] expr)
               (-> [arrtype_in ...] arrtype_out)
               [env-entry_2 ...] archive_2
               (apply-env/e:atom [env-entry_2 ... (?i var_sm) env-entry_3 ...]
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
  [(where ([env-entry_1 ...] (Array atmtype_fun shp_fun))
     (articulate-array-type [env-entry_0 ...] arrtype))
   (synth-app [env-entry_1 ... (^ tvar) ...] archive_0
              (t-app e:expr_fp (^ tvar) ...)
              (subst* (Array atmtype_fun {++ shp_all shp_fun})
                      [(tvar (^ tvar)) ...])
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              e:expr_fm [e:expr_arg ...])
   --- app:∀
   (synth-app [env-entry_0 ...] archive_0
              e:expr_fp (Array (∀ [tvar ...] arrtype) shp_all)
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              (apply-env/e:expr env_1 e:expr_fm)
              [e:expr_arg ...])]
  [(where ([env-entry_1 ...] (Array atmtype_fun shp_fun))
     (articulate-array-type [env-entry_0 ...] arrtype))
   (synth-app [env-entry_1 ... (^ ivar) ...] archive_0
              (i-app e:expr_fp (^ ivar) ...)
              (subst* (Array atmtype_fun {++ shp_all shp_fun})
                      [(ivar (^ ivar)) ...])
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              e:expr_fm [e:expr_arg ...])
   --- app:Π
   (synth-app [env-entry_0 ...] archive_0
              e:expr_fp (Array (Π [ivar ...] arrtype) shp_all)
              [expr_arg ...]
              arrtype_out
              env_1 archive_1
              (apply-env/e:expr env_1 e:expr_fm)
              [e:expr_arg ...])]
  ;; Applying a monomorphic unary function array, where the function array
  ;; provides the principal frame
  [(side-condition ,(not (term (cell-polymorphic? (Array atmtype_in shp_in)))))
   (where svar_afrm ,(gensym '@AFRM))
   (where svar_aext ,(gensym '@AEXT))
   (check/expr [env-entry_0 ... (^ svar_afrm) (^ svar_aext)] archive_0
               expr_arg (Array atmtype_in {++ (^ svar_afrm) shp_in})
               env_1 archive_1
               e:expr_arg)
   (equate env_1 archive_1 shp_fun {++ (^ svar_afrm) (^ svar_aext)}
           env_2 archive_2)
   ;; If both the function and argument arrays have the same frame shape, then
   ;; we might use either app:->*f or app:->*a. Prune off this version in that
   ;; case, to reduce redundant derivation search.
   (side-condition
    ,(not (redex-match? Remora-elab {Shp}
                        (term (Inormalize-idx (apply-env/e:idx
                                               env_2 (^ svar_aext)))))))
   ;; Imagine we have a curried function. After consuming only this first
   ;; argument, what shape does the function array have? That is the "frame
   ;; shape so far" at this point in processing the whole n-ary application.
   (synth-app env_2 archive_2
              e:expr_fun
              (Array (-> [arrtype_rest ...] arrtype_out) shp_fun)
              [expr_rest ...]
              arrtype_result
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
                         arrtype_out)
                     shp_fun)
              [expr_arg expr_rest ...]
              arrtype_result
              env_3 archive_3
              e:expr_fm [e:expr_arg e:expr_rest ...])]
  ;; Applying a monomorphic unary function array, where the argument array
  ;; provides the principal frame
  [(side-condition ,(not (term (cell-polymorphic? (Array atmtype_in shp_in)))))
   (where svar_afrm ,(gensym '@AFRM))
   (where svar_fext ,(gensym '@FEXT))
   (check/expr [env-entry_0 ... (^ svar_afrm) (^ svar_fext)] archive_0
               expr_arg (Array atmtype_in {++ (^ svar_afrm) shp_in})
               env_1 archive_1
               e:expr_arg)
   (equate env_1 archive_1 (^ svar_afrm) {++ shp_fun (^ svar_fext)}
           env_2 archive_2)
   (synth-app env_2 archive_2
              e:expr_fun
              (Array (-> [arrtype_rest ...] arrtype_out) (^ svar_afrm))
              [expr_rest ...]
              arrtype_result
              env_3 archive_3
              e:expr_fm [e:expr_rest ...])
   --- app:->*a
   (synth-app [env-entry_0 ...] archive_0
              e:expr_fun
              (Array (-> [(Array atmtype_in shp_in) arrtype_rest ...]
                         arrtype_out)
                     shp_fun)
              [expr_arg expr_rest ...]
              arrtype_result
              env_3 archive_3
              e:expr_fm [e:expr_arg e:expr_rest ...])]
  ;; Applying a monomorphic unary function array, where the expected input type
  ;; mandates a scalar frame
  [(side-condition (cell-polymorphic? arrtype_in))
   (check/expr env_0 archive_0
               expr_arg arrtype_in
               env_1 archive_1 e:expr_arg)
   (synth-app env_1 archive_1
              e:expr_fun
              (Array (-> [arrtype_rest ...]
                         arrtype_out)
                     shp_fun)
              [expr_rest ...]
              arrtype_result
              env_2 archive_2
              e:expr_fm [e:expr_rest ...])
   --- App:->*c
   (synth-app env_0 archive_0
              e:expr_fun
              (Array (-> [arrtype_in arrtype_rest ...]
                         arrtype_out)
                     shp_fun)
              [expr_arg expr_rest ...]
              arrtype_result
              env_2 archive_2
              e:expr_fm [e:expr_arg e:expr_rest ...])]
  [(where (env_1 (Array atmtype_out shp_out))
     (articulate-array-type env_0 arrtype_out))
   --- app:->0
   (synth-app env_0 archive_0
              e:expr_fun
              (Array (-> [] arrtype_out)
                     shp_fun)
              []
              (Array atmtype_out {++ shp_fun shp_out})
              env_1 archive_0
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
  [--- sub:exatmvar
   (subtype/atom env archive exatmvar exatmvar env archive hole)]

  [;; TODO: occurs check
   (side-condition
    ,(not (redex-match?
           Remora-elab
           [(^ atmvar) (^ atmvar)]
           (term [exatmvar atmtype]))))
   (instL/atom env_0 archive_0 exatmvar atmtype env_1 archive_1 e:actx)
   --- sub:instL/atom
   (subtype/atom env_0 archive_0
                 exatmvar atmtype
                 env_1 archive_1 e:actx)]
  [;; TODO: occurs check
   ;; If both types are existential variables, we can just use sub:instL/atom,
   ;; so allowing this as well would lead to lots of redundant backtracking.
   (side-condition
    ,(not (redex-match? Remora-elab (^ atmvar) (term atmtype))))
   (instR/atom env_0 archive_0 atmtype exatmvar env_1 archive_1 e:actx)
   --- sub:instR/atom
   (subtype/atom env_0 archive_0
                 atmtype exatmvar
                 env_1 archive_1 e:actx)])
(define-judgment-form Remora-elab
  ;; TODO: sub:ΣL, sub:ΣR
  #:mode (subtype/expr I I I I O O O)
  #:contract (subtype/expr env archive arrtype arrtype env archive e:ectx)
  [;; TODO: occurs check
   (side-condition
    ,(not (redex-match?
           Remora-elab
           [(^ arrvar) (^ arrvar)]
           (term [exatmvar atmtype]))))
   (instL/array env_0 archive_0 exarrvar arrtype env_1 archive_1 e:ectx)
   --- sub:instL/array
   (subtype/expr env_0 archive_0 exarrvar arrtype env_1 archive_1 e:ectx)]
  [;; TODO: occurs check
   (side-condition
    ,(not (redex-match?
           Remora-elab
           [(^ arrvar) (^ arrvar)]
           (term [exatmvar atmtype]))))
   (instR/array env_0 archive_0 arrtype exarrvar env_1 archive_1 e:ectx)
   --- sub:instR/array
   (subtype/expr env_0 archive_0 arrtype exarrvar env_1 archive_1 e:ectx)]
  [--- sub:arrvar
   (subtype/expr env archive arrvar arrvar env archive hole)]
  [--- sub:exarrvar
   (subtype/expr env archive exarrvar exarrvar env archive hole)]
  [(equate env_0 archive_0 shp_fl shp_fh env_1 archive_1)
   (subtype/exprs env_1 archive_1
                  [arrtype_inh ...] [arrtype_inl ...]
                  env_2 archive_2 [e:ectx_in ...])
   (subtype/expr env_2 archive_2
                 arrtype_outl arrtype_outh
                 env_3 archive_3 e:ectx_out)
   --- sub:->*
   (subtype/expr env_0 archive_0
                 (Array (-> [arrtype_inl ...] arrtype_outl) shp_fl)
                 (Array (-> [arrtype_inh ...] arrtype_outh) shp_fh)
                 env_3 archive_3
                 (fn-coercion [arrtype_inl ...] [arrtype_inh ...] arrtype_outl
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
    [env-entry_1 ... tvar ... env-entry_2 ...] archive_1 e:ectx)
   --- sub:∀R
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array atmtype_lo shp_lo)
    (Array (∀ [tvar ...] (Array atmtype_hi shp_c)) shp_f)
    [env-entry_1 ...] archive_1
    ;; Each shp_c cell needs to get wrapped in the ∀ by tη expansion
    (coerce-each
     (Array atmtype_lo shp_c)
     (array {}
            [(tλ [(tvar->bind tvar) ...]
                (coerce-each (Array atmtype_lo {Shp}) e:ectx))]))
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
    [env-entry_1 ... ivar ... _ ...] archive_1 e:ectx)
   --- sub:ΠR
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array atmtype_lo shp_lo)
    (Array (Π [ivar ...] (Array atmtype_hi shp_c)) shp_f)
    [env-entry_1 ...] archive_1
    ;; Each shp_c cell needs to get wrapped in the ∀ by iη expansion
    ((array
      {}
      [(λ ((c (Array atmtype_hi shp_c)))
         (array {} [(iλ [(ivar->bind ivar) ...] c)]))])
     e:ectx))]
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
                                    (Σ [(ivar->bind ivar) ...] (Array atmtype_hi shp_c)))}))))]
  [(where [(atmvar_in svar_in) ...]
     ,(build-list
       (length (term [arrtype_in ...]))
       (λ (n) (list
               (gensym (format "&~a-in~a-"
                               (substring (symbol->string (term atmvar)) 1)
                               n))
               (gensym (format "@~a-in~a-"
                               (substring (symbol->string (term atmvar)) 1)
                               n))))))
   (where atmvar_out
     ,(gensym (format "&~a-out"
                      (substring (symbol->string (term atmvar)) 1))))
   (where svar_out
     ,(gensym (format "@~a-out"
                      (substring (symbol->string (term atmvar)) 1))))
   (subtype/expr [env-entry_l ...
                  (^ atmvar_in) ... (^ svar_in) ... (^ atmvar_out) (^ svar_out)
                  (^ atmvar (-> [(Array (^ atmvar_in) (^ svar_in)) ...]
                                (Array (^ atmvar_out) (^ svar_out))))
                  env-entry_r ...]
                 archive_0
                 (Array (-> [(Array (^ atmvar_in) (^ svar_in)) ...]
                            (Array (^ atmvar_out) (^ svar_out)))
                        shp_lo)
                 (Array (-> [arrtype_in ...] arrtype_out) shp_hi)
                 env_1 archive_1
                 e:ectx)
   --- sub:->instL
   (subtype/expr [env-entry_l ... (^ atmvar) env-entry_r ...]
                 archive_0
                 (Array (^ atmvar) shp_lo)
                 (Array (-> [arrtype_in ...] arrtype_out) shp_hi)
                 env_1 archive_1 e:ectx)]
  [(where [(atmvar_in svar_in) ...]
     ,(build-list
       (length (term [arrtype_in ...]))
       (λ (n) (list
               (gensym (format "&~a-in~a-"
                               (substring (symbol->string (term atmvar)) 1)
                               n))
               (gensym (format "@~a-in~a-"
                               (substring (symbol->string (term atmvar)) 1)
                               n))))))
   (where atmvar_out
     ,(gensym (format "&~a-out"
                      (substring (symbol->string (term atmvar)) 1))))
   (where svar_out
     ,(gensym (format "@~a-out"
                      (substring (symbol->string (term atmvar)) 1))))
   (subtype/expr [env-entry_l ...
                  (^ atmvar_in) ... (^ svar_in) ... (^ atmvar_out) (^ svar_out)
                  (^ atmvar (-> [(Array (^ atmvar_in) (^ svar_in)) ...]
                                (Array (^ atmvar_out) (^ svar_out))))
                  env-entry_r ...]
                 archive_0
                 (Array (-> [arrtype_in ...] arrtype_out) shp_hi)
                 (Array (-> [(Array (^ atmvar_in) (^ svar_in)) ...]
                            (Array (^ atmvar_out) (^ svar_out)))
                        shp_lo)
                 env_1 archive_1
                 e:ectx)
   --- sub:->instR
   (subtype/expr [env-entry_l ... (^ atmvar) env-entry_r ...]
                 archive_0
                 (Array (-> [arrtype_in ...] arrtype_out) shp_hi)
                 (Array (^ atmvar) shp_lo)
                 env_1 archive_1 e:ectx)]
  ;; After destructuring the atom type as much as possible, we can conclude that
  ;; [T_1 S_1] <: [T_2 S_2] by making sure T_1 <: T_2 and S_1 ≐ S_2. The
  ;; resulting coercion will be ugly. It must apply an η-expanded version of the
  ;; atom coercion (but there doesn't seem to be much that can be done with atom
  ;; coercions because atom-level computation is so restricted).
  [(subtype/atom env_0 archive_0
                 (apply-env/type env_0 atmtype_0)
                 (apply-env/type env_0 atmtype_1)
                 env_1 archive_1 e:actx)
   (equate env_1 archive_1 shp_0 shp_1 env_2 archive_2)
   --- sub:Array
   (subtype/expr env_0 archive_0
                 (Array atmtype_0 shp_0)
                 (Array atmtype_1 shp_1)
                 env_2 archive_2
                 (lift-atom-coercion atmtype_0 e:actx))])

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
  [(where [tvar_in ...]
     ,(build-list (length (term [arrtype_in ...]))
                  (λ (n) (gensym (format "*~a-in~a_"
                                         (substring (symbol->string (term tvar)) 1)
                                         n)))))
   (where tvar_out ,(gensym (format "*~a-out_"
                                    (substring (symbol->string (term tvar)) 1))))
   (where svar_frm ,(gensym (format "@~a-frm_"
                                    (substring (symbol->string (term tvar)) 1))))
   (instR/arrays [env-entry_l ...
                  (^ tvar_in) ... (^ tvar_out) (^ svar_frm)
                  (^ tvar (Array (-> [(^ tvar_in) ...] (^ tvar_out)) (^ svar_frm)))
                  env-entry_r ...]
                 archive_0
                 [arrtype_in ...] [(^ tvar_in) ...]
                 env_1 archive_1 [e:ectx_in ...])
   (instL/array env_1 archive_1 (^ tvar_out) arrtype_out
                env_2 archive_2 e:ectx_out)
   (equate env_2 archive_2 (^ svar_frm) shp_f env_3 archive_3)
   --- ArrL:->*
   (instL/array [env-entry_l ... (^ tvar) env-entry_r ...] archive_0
                (^ tvar) (Array (-> [arrtype_in ...] arrtype_out) shp_f)
                env_3 archive_3
                (fn-coercion [(^ tvar_in) ...] [arrtype_in ...] (^ tvar_out)
                             [e:ectx_in ...] e:ectx_out))]
  [#;(side-condition ,(printf "Monotype check on ~v: ~v\n"
                            (term atmtype)
                            (term (monotype? atmtype))))
   #;(where #t (monotype? atmtype))
   (where exatmvar (^ ,(gensym '&elt_)))
   ;(side-condition ,(printf "New env entry: ~v\n" (term exatmvar)))
   (where exsvar (^ ,(gensym '@shp_)))
   ;(side-condition ,(printf "New env entry: ~v\n" (term exsvar)))
   (instL/atom [env-entry_l ...
                exatmvar exsvar (^ tvar (Array exatmvar exsvar))
                env-entry_r ...]
               archive_0
               exatmvar atmtype
               env_1 archive_1 e:actx)
   (equate env_1 archive_1 exsvar shp env_2 archive_2)
   --- ArrL:array
   (instL/array [env-entry_l ... (^ tvar) env-entry_r ...]
                archive_0
                (^ tvar) (Array atmtype shp)
                env_2 archive_2
                (lift-atom-coercion exatmvar e:actx))]
  [(instL/array [env-entry_0 ... tvar_a ...] archive_0
                (^ tvar) (Array atmtype {++ shp_f shp_c})
                [env-entry_1 ... tvar_a ... _ ...] archive_1 e:ectx)
   --- ArrL:∀*
   (instL/array [env-entry_0 ...] archive_0
                (^ tvar) (Array (∀ [tvar_a ...] (Array atmtype shp_c)) shp_f)
                [env-entry_1 ...] archive_1
                (in-hole (coerce-each
                          (Array atmtype shp_c)
                          (array {} [(tλ [(tvar->bind tvar_a) ...] hole)]))
                         e:ectx))]
  [(instL/array [env-entry_0 ... ivar_a ...] archive_0
                (^ tvar) (Array atmtype {++ shp_f shp_c})
                [env-entry_1 ... ivar_a ... _ ...] archive_1 e:ectx)
   --- ArrL:Π*
   (instL/array [env-entry_0 ...] archive_0
                (^ tvar) (Array (Π [ivar_a ...] (Array atmtype shp_c)) shp_f)
                [env-entry_1 ...] archive_1
                (in-hole (coerce-each
                          (Array atmtype shp_c)
                          (array {} [(iλ [(ivar->bind ivar_a) ...] hole)]))
                         e:ectx))])

(define-judgment-form Remora-elab
  #:mode (instR/array I I I I O O O)
  #:contract (instR/array env archive arrtype exarrvar env archive e:ectx)
  ;;----------------------------------------------------------------------------
  ;; "Structural" rules
  ;;----------------------------------------------------------------------------
  [(kind-array [env-entry_l ...] monotype)
   --- ArrR:solve
   (instR/array [env-entry_l ... (^ tvar) env-entry_r ...] archive
                monotype (^ tvar)
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
  [(where [tvar_in ...]
     ,(build-list (length (term [arrtype_in ...]))
                  (λ (n) (gensym (format "*~a-in~a_"
                                         (substring (symbol->string (term tvar)) 1)
                                         n)))))
   (where tvar_out ,(gensym (format "*~a-out_"
                                    (substring (symbol->string (term tvar)) 1))))
   (where svar_frm ,(gensym (format "@~a-frm_"
                                    (substring (symbol->string (term tvar)) 1))))
   (instL/arrays [env-entry_l ...
                  (^ tvar_in) ... (^ tvar_out) (^ svar_frm)
                  (^ tvar (Array (-> [(^ tvar_in) ...] (^ tvar_out)) (^ svar_frm)))
                  env-entry_r ...]
                 archive_0
                 [(^ tvar_in) ...] [arrtype_in ...]
                 env_1 archive_1 [e:ectx_in ...])
   (instR/array env_1 archive_1 arrtype_out (^ tvar_out)
                env_2 archive_2 e:ectx_out)
   (equate env_2 archive_2 (^ svar_frm) shp_f env_3 archive_3)
   --- ArrR:->*
   (instR/array [env-entry_l ... (^ tvar) env-entry_r ...] archive_0
                (Array (-> [arrtype_in ...] arrtype_out) shp_f) (^ tvar)
                env_3 archive_3
                (fn-coercion [(^ tvar_in) ...] [arrtype_in ...] arrtype_out
                             [e:ectx_in ...] e:ectx_out))]
  [(where exatmvar (^ ,(gensym '&elt_)))
   (where exsvar (^ ,(gensym '@shp_)))
   (instR/atom [env-entry_l ...
                exatmvar exsvar (^ tvar (Array exatmvar exsvar))
                env-entry_r ...]
               archive_0
               atmtype exatmvar
               env_1 archive_1 e:actx)
   (equate env_1 archive_1 exsvar shp env_2 archive_2)
   --- ArrR:array
   (instR/array [env-entry_l ... (^ tvar) env-entry_r ...] archive_0
                (Array atmtype shp) (^ tvar)
                env_2 archive_2
                (lift-atom-coercion atmtype e:actx))]
  [(where var_sm ,(gensym 'SM_))
   (instR/array [env-entry_0 ...
                 (^ tvar)
                 env_entry_1 ...
                 (?i var_sm)
                 (^ tvar_a) ...] archive_0
                (subst* (Array atmtype {++ shp_f shp_c})
                        [(tvar_a (^ tvar_a)) ...])
                (^ tvar)
                env_1 archive_1 e:ectx)
   (where [env-entry_2 ... (?i var_sm) _ ...] env_1)
   --- ArrR:∀*
   (instR/array [env-entry_0 ... (^ tvar) env_entry_1 ...] archive_0
                (Array (∀ [tvar_a ...] (Array atmtype shp_c)) shp_f) (^ tvar)
                [env-entry_2 ...] archive_1
                (apply-env/e:ectx env_1 (in-hole e:ectx (t-app hole (^ tvar_a) ...))))]
  [(where var_sm ,(gensym 'SM_))
   (instR/array [env-entry_0 ...
                 (^ tvar)
                 env_entry_1 ...
                 (?i var_sm)
                 (^ ivar_a) ...] archive_0
                (subst* (Array atmtype {++ shp_f shp_c})
                        [(ivar_a (^ ivar_a)) ...])
                (^ tvar)
                env_1 archive_1 e:ectx)
   (where [env-entry_2 ... (?i var_sm) _ ...] env_1)
   --- ArrR:Π*
   (instR/array [env-entry_0 ... (^ tvar) env_entry_1 ...] archive_0
                (Array (∀ [ivar_a ...] (Array atmtype shp_c)) shp_f) (^ ivar)
                [env-entry_2 ...] archive_1
                (apply-env/e:ectx env_1 (in-hole e:ectx (i-app hole (^ ivar_a) ...))))])


;;; Provide a judgment-form version of the logic used to interpret the solver's
;;; results. The actual index-equating judgment is wrapped to ensure it only
;;; sees normalized indices.
(define-judgment-form Remora-elab
  #:mode (equate I I I I O O)
  #:contract (equate env archive idx idx env archive)
  [#;(side-condition ,(printf "Equating ~v and ~v\n" (term idx_0) (term idx_1)))
   (equate/n env_0 archive_0
             (Inormalize-idx (apply-env/e:idx env_0 idx_0))
             (Inormalize-idx (apply-env/e:idx env_0 idx_1))
             env_1 archive_1)
   --- equate:normalize
   (equate env_0 archive_0 idx_0 idx_1 env_1 archive_1)])
;;; TODO: Add "trimming" rules that match up dim* prefixes or suffixes so they
;;; don't have to be dealt with by the solver.
(define-judgment-form Remora-elab
  #:mode (equate/n I I I I O O)
  #:contract (equate/n env archive nidx nidx env archive)
  ;; Are both sides syntactically equal?
  [--- equate:≡
   (equate/n env archive shp shp env archive)]
  ;; Is one side a shape variable?
  [(sort-shp [env-entry_l ...] shp)
   --- equate:solveL/shp
   (equate/n [env-entry_l ... (^ svar) env-entry_r ...] archive_0
           (^ svar) shp
           [env-entry_l ... (^ svar shp) env-entry_r ...] archive_0)]
  [(sort-shp [env-entry_l ...] shp)
   --- equate:solveR/shp
   (equate/n [env-entry_l ... (^ svar) env-entry_r ...] archive_0
           shp (^ svar)
           [env-entry_l ... (^ svar shp) env-entry_r ...] archive_0)]
  ;; Is one side a dim variable?
  [(sort-dim [env-entry_l ...] dim)
   --- equate:solveL/dim
   (equate/n [env-entry_l ... (^ dvar) env-entry_r ...] archive_0
           (^ dvar) dim
           [env-entry_l ... (^ dvar dim) env-entry_r ...] archive_0)]
  [(sort-dim [env-entry_l ...] dim)
   --- equate:solveR/dim
   (equate/n [env-entry_l ... (^ dvar) env-entry_r ...] archive_0
           dim (^ dvar)
           [env-entry_l ... (^ dvar dim) env-entry_r ...] archive_0)]
  ;; Can we peel a dim off one end?
  [(where (dim_0 shp_l0) (split-left-dim shp_0))
   (where (dim_1 shp_r0) (split-left-dim shp_1))
   (equate/n env_0 archive_0 dim_0 dim_1 env_1 archive_1)
   (equate/n env_1 archive_1 shp_l0 shp_r0 env_2 archive_2)
   --- equate:trimL/dim
   (equate/n env_0 archive_0 shp_0 shp_1 env_2 archive_2)]
  [(where (shp_l0 dim_0) (split-right-dim shp_0))
   (where (shp_r0 dim_1) (split-right-dim shp_1))
   (equate/n env_0 archive_0 dim_0 dim_1 env_1 archive_1)
   (equate/n env_1 archive_1 shp_l0 shp_r0 env_2 archive_2)
   --- equate:trimR/dim
   (equate/n env_0 archive_0 shp_0 shp_1 env_2 archive_2)]
  ;; Can we peel svars off the ends?
  [(equate/n env_0 archive_0 {++ shp_0 ...} {++ shp_1 ...} env_2 archive_2)
   --- equate:trimL/svar
   (equate/n env_0 archive_0
             {++ svar shp_0 ...}
             {++ svar shp_1 ...}
             env_2 archive_2)]
  [(equate/n env_0 archive_0 {++ shp_0 ...} {++ shp_1 ...} env_2 archive_2)
   --- equate:trimR/svar
   (equate/n env_0 archive_0
             {++ shp_0 ... svar}
             {++ shp_1 ... svar}
             env_2 archive_2)]
  ;; Ask an ILP solver whether dim_0 and dim_1 can be equated and what values
  ;; must be assigned to their unsolved existential variables in order to do so.
  [(side-condition
    ;; Make sure the shapes we have don't match some shortcut rule before we
    ;; hand them off to the Makanin solver.
    ,(nor
      ;; trivial case
      (redex-match? Remora-elab [shp shp] (term [shp_0 shp_1]))
      ;; directly solvable cases
      (term (resolvable-shp? env_0 shp_0 shp_1))
      (term (resolvable-shp? env_0 shp_1 shp_0))
      ;; dimension peel cases
      (and (redex-match? Remora-elab (dim shp) (term (split-left-dim shp_0)))
           (redex-match? Remora-elab (dim shp) (term (split-left-dim shp_1))))
      (and (redex-match? Remora-elab (shp dim) (term (split-right-dim shp_0)))
           (redex-match? Remora-elab (shp dim) (term (split-right-dim shp_1))))
      ;; svar peel cases
      (and (redex-match? Remora-elab {++ svar _ ...} (term shp_0))
           (redex-match? Remora-elab {++ svar _ ...} (term shp_1)))
      (and (redex-match? Remora-elab {++ _ ... svar} (term shp_0))
           (redex-match? Remora-elab {++ _ ... svar} (term shp_1)))))
   (where (_ ... (env_1 archive_1) _ ...)
     (equate-shapes env_0 archive_0
                    (apply-env/e:idx env_0 shp_0)
                    (apply-env/e:idx env_0 shp_1)))
   --- equate:shp
   (equate/n env_0 archive_0 shp_0 shp_1 env_1 archive_1)]
  ;; For a singleton shape, the solver has no tricky decisions to make.
  [(where (_ ... (env_1 archive_1) _ ...)
     (equate-shapes env_0 archive_0
                    (apply-env/e:idx env_0 {Shp dim_0})
                    (apply-env/e:idx env_0 {Shp dim_1})))
   --- equate:dim
   (equate/n env_0 archive_0 dim_0 dim_1 env_1 archive_1)])
;;; Metafunction wrapper for solver call
(define-metafunction Remora-elab
  equate-shapes : env archive shp shp -> [(env archive) ...]
  [(equate-shapes env archive shp_0 shp_1)
   ,(begin
      ;(printf "Initial environment:\n~v\n" (term env))
      ;(printf "Initial archive:\n~v\n" (term archive))
      ;(printf "Left shape:\n~v\n" (term shp_0))
      ;(printf "Right shape:\n~v\n" (term shp_1))
      (stream->list (solutions (term env) (term archive)
                               (term shp_0) (term shp_1))))])

;; Is the first shape an existential variable that can be resolved as the
;; second shape in the given environment?
(define-metafunction Remora-elab
  resolvable-shp? : env shp shp -> boolean
  [(resolvable-shp? [env-entry_l ... exsvar env-entry_r ...] exsvar shp)
   ,(judgment-holds (sort-shp [env-entry_l ...] shp))]
  [(resolvable-shp? _ _ _) #f])

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
   (check/atoms env_1 archive_1 [atom_1 atom_2 ...] atmtype_join env_n archive_n [e:atom_1 ...])
   ;; TODO: replace with join operation on types with exvars
   --- syn*
   (synth/atoms env_0 archive_0 [atom_0 atom_1 atom_2 ...] atmtype_join
                env_n archive_n [e:atom_0 e:atom_1 ...])])

(define-judgment-form Remora-elab
  #:mode (synth/exprs I I I O O O O)
  #:contract (synth/exprs env archive [expr ...+] arrtype env archive [e:expr ...+])
  [(synth/expr env_0 archive_0 expr arrtype env_1 archive_1 e:expr)
   --- syn*:base
   (synth/exprs env_0 archive_0 [expr] arrtype env_1 archive_1 [e:expr])]
  [(synth/expr env_0 archive_0 expr_0 arrtype_join env_1 archive_1 e:expr_0)
   (check/exprs env_1 archive_1 [expr_1 expr_2 ...] arrtype_join env_n archive_n [e:expr_1 ...])
   ;; TODO: replace with join operation on types with exvars
   --- syn*
   (synth/exprs env_0 archive_0 [expr_0 expr_1 expr_2 ...] arrtype_join
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
  [--- atmR*:base
   (instR/arrays env archive [] [] env archive [])]
  [(instR/array env_0 archive_0 arrtype_0 (^ arrvar_0) env_1 archive_1 e:ectx_0)
   (instR/arrays env_1 archive_1
                 [arrtype_1 ...] [(^ arrvar_1) ...]
                 env_2 archive_2 [e:ectx_1 ...])
   --- atmR*
   (instR/arrays env_0 archive_0
                 [arrtype_0 arrtype_1 ...] [(^ arrvar_0) (^ arrvar_1) ...]
                 env_2 archive_2 [e:ectx_0 e:ectx_1 ...])])



;;;;----------------------------------------------------------------------------
;;;; Demo cases
;;;;----------------------------------------------------------------------------
(module+ demo
  (define-syntax-rule
    (test description check ...)
    (begin (displayln description)
           check ...
           (printf "\n\n")))

  (test "simple application"
        (judgment-holds
         (synth/expr [(+ (DR (-> [Int Int] Int)))] []
                     (+ (array {} [40]) (array {} [2]))
                     type env archive e:expr)
         {type env archive e:expr}))
  
  (test "vector + scalar -- identify frame"
   (judgment-holds
    (synth/expr [(+ (DR (-> [Int Int] Int)))] []
                (+ (array {3} [4 5 6]) (array {} [2]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "vector + matrix -- identify frame"
   (judgment-holds
    (synth/expr [(+ (DR (-> [Int Int] Int)))] []
                (+ (array {3} [100 200 300])
                   (array {3 4} [1 2 3 4 5 6 7 8 9 10 11 12]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "MISD -- identify frame"
   (judgment-holds
    (synth/expr [(+ (DR (-> [Int Int] Int)))
                 (- (DR (-> [Int Int] Int)))
                 (* (DR (-> [Int Int] Int)))]
                []
                ((frame {3} [+ * -]) (array {} [10]) (array {} [5]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "mismatched vector + vector -- unsatisfiable shape constraint"
   (judgment-holds
    (synth/expr [(+ (DR (-> [Int Int] Int)))] []
                (+ (array {3} [4 5 6]) (array {8} [1 2 3 4 5 6 7 8]))
                type env archive e:expr)
    archive))
  
  (test "id0 -- generate monotype with atmtype hole"
   (judgment-holds
    (synth/atom [] []
                (λ [(x 0)] x)
                type env archive e:atom)
    {type env archive e:atom}))
  
  (test "id2 -- generate monotype with atmtype hole and two dim holes"
   (judgment-holds
    (synth/atom [] []
                (λ [(x 2)] x)
                type env archive e:atom)
    {type env archive e:atom}))
  
  (test "id∞ -- generate monotype with atmtype hole and shp hole"
   (judgment-holds
    (synth/atom [] []
                (λ [(x all)] x)
                type env archive e:atom)
    {type env archive e:atom}))
  
  (test "apply id0 -- selecting atom type"
   (judgment-holds
    (synth/expr [] []
                ((array {} [(λ [(x 0)] x)])
                 (array {} [#t]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "id0 -- selecting atom type and frame shape"
   (judgment-holds
    (synth/expr [] []
                ((array {} [(λ [(x 0)] x)])
                 (array {2 3} [10 20 30 40 50 60]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "apply id2 -- selecting atom type and two cell dims"
   (judgment-holds
    (synth/expr [] []
                ((array {} [(λ [(x 2)] x)])
                 (array {2 3} [10 20 30 40 50 60]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "apply id∞ -- selecting array type"
   (judgment-holds
    (synth/expr [] []
                ((array {} [(λ [(x all)] x)])
                 (array {2 3} [10 20 30 40 50 60]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "construct ∀id0 -- generalize atmtype hole"
   (judgment-holds
    (synth/atom [] []
                ((λ [(x 0)] x)
                 : (∀ [&t] (Array (-> [(Array &t (Shp))]
                                      (Array &t (Shp))) (Shp))))
                type env archive e:atom)
    {type env archive e:atom}))
  
  (test "construct ∀id∞ -- generalize arrtype hole"
   (judgment-holds
    (synth/atom [] []
                ((λ [(x all)] x)
                 : (∀ [*t] (Array (-> [*t] *t) (Shp))))
                type env archive e:atom)
    {type env archive e:atom}))
  
  (test "alternative (shape monomorphic) ∀id∞ -- generalize atmtype hole, retain shp hole"
   (judgment-holds
    (synth/atom [] []
                ((λ [(x all)] x)
                 : (∀ [&t] (Array (-> [(Array &t (Shp))] (Array &t (Shp))) (Shp))))
                type env archive e:atom)
    {type env archive e:atom}))
  
  (test "apply ∀id0 -- generalize, then select atom type argument"
   (judgment-holds
    (synth/expr [] []
                ((array {} [((λ [(x 0)] x)
                             : (∀ [&t] (Array (-> [(Array &t (Shp))]
                                                  (Array &t (Shp))) (Shp))))])
                 (array {} [5]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "lift ∀id0 -- generalize, then select atom type argument and frame shape"
   (judgment-holds
    (synth/expr [] []
                ((array {} [((λ [(x 0)] x)
                             : (∀ [&t] (Array (-> [(Array &t (Shp))]
                                                  (Array &t (Shp))) (Shp))))])
                 (array {3} [5 10 15]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "apply ∀id∞ -- generalize, then select array type argument"
   (judgment-holds
    (synth/expr [] []
                ((array {} [((λ [(x all)] x)
                             : (∀ [*t] (Array (-> [*t] *t) (Shp))))])
                 (array {3} [5 10 15]))
                type env archive e:expr)
    {type env archive e:expr}))
  
  (test "construct ∀Πid∞ -- generalize arrtype hole"
   (judgment-holds
    (synth/atom [] []
                ((λ [(x all)] x)
                 : (∀ [&t]
                     (Array
                      (Π [@t]
                        (Array (-> [(Array &t @t)] (Array &t @t)) (Shp))) (Shp))))
                type env archive e:atom)
    {type env archive e:atom}))
  
  (test "annotate extra arg -- recognize arity mismatch"
   (judgment-holds
    (synth/atom [&t] []
                ((λ [(x 0)] x)
                 : (-> [(Array &t (Shp))
                        (Array &t (Shp))]
                       (Array &t (Shp))))
                _ _ _ _)))
  
  (test "pass too few args -- recognize arity mismatch"
   (judgment-holds
    (synth/expr [] []
                ((array {} [(λ [(x 0) (y 0)] x)])
                 (array {} [7]))
                _ _ _ _)))
  
  (test "pass too many args -- recognize arity mismatch"
   (judgment-holds
    (synth/expr [] []
                ((array {} [(λ [(x 0) (y 0)] x)])
                 (array {} [5])
                 (array {} [6])
                 (array {} [7]))
                _ _ _ _)))
  
  (test "outer product -- identify two frames and a cell shape"
   (judgment-holds
    (synth/expr [(* (DR (-> [Int Int] Int)))]
                []
                ((rerank [0 1] *)
                 (array {3} [10 20 30])
                 (array {2} [5 6]))
                type env archive e:expr)
    {type env archive e:expr}))

  (test "length -- select shape and dim arguments"
        (judgment-holds
         (synth/expr [(length (DR (∀ [&t] (Π [$l @c] (-> [[&t $l @c]] Int)))))]
                     []
                     (length (array {4 2 3}
                                    [ 1  2  3  4  5  6
                                      7  8  9 10 11 12
                                     13 14 15 16 17 18
                                     19 20 21 22 23 24]))
                     type env archive e:expr)
         {type env archive e:expr}))
  
  (test "vector norm -- instantiate polymorphic function"
        (judgment-holds
         (synth/atom [(sqrt (DR (-> [Int] Int)))
                      (* (DR (-> [Int Int] Int)))
                      (+ (DR (-> [Int Int] Int)))
                      (reduce/0 (DR (∀ [&t]
                                      (Π [$l @c]
                                        (-> [(-> [[&t @c] [&t @c]] [&t @c])
                                             [&t @c]
                                             [&t $l @c]]
                                            [&t @c])))))]
                     []
                     (λ [(v 1)] (sqrt (reduce/0 + (scl 0) (* v v))))
                     type env archive e:atom)
         {type env archive e:atom}))
  
  (test "nonempty vector norm -- instantiate polymorphic function, propagate length constraint"
        ;; The resulting type looks agnostic about input length, but using
        ;; an argument that's too short leads to an UNSAT constraint archive.
        (judgment-holds
         (synth/atom [(sqrt (DR (-> [Int] Int)))
                      (* (DR (-> [Int Int] Int)))
                      (+ (DR (-> [Int Int] Int)))
                      (reduce (DR (∀ [&t]
                                    (Π [$l @c]
                                      (-> [(-> [[&t @c] [&t @c]] [&t @c])
                                           [&t (+ 1 $l) @c]]
                                          [&t @c])))))]
                     []
                     (λ [(v 1)] (sqrt (reduce + (* v v))))
                     type env archive e:atom)
         {type env archive e:atom}))
  (test "applying length-restricted norm -- length constraint SAT"
        (judgment-holds
         (synth/expr [(sqrt (DR (-> [Int] Int)))
                      (* (DR (-> [Int Int] Int)))
                      (+ (DR (-> [Int Int] Int)))
                      (reduce (DR (∀ [&t]
                                    (Π [$l @c]
                                      (-> [(-> [[&t @c] [&t @c]] [&t @c])
                                           [&t (+ 1 $l) @c]]
                                          [&t @c])))))]
                     []
                     ((scl (λ [(v 1)] (sqrt (reduce + (* v v)))))
                      (array {2} [4 3]))
                     type env archive e:expr)
         {type env archive e:expr}))
  (test "mis-applying length-restricted norm -- length constraint UNSAT"
        (judgment-holds
         (synth/expr [(sqrt (DR (-> [Int] Int)))
                      (* (DR (-> [Int Int] Int)))
                      (+ (DR (-> [Int Int] Int)))
                      (reduce (DR (∀ [&t]
                                    (Π [$l @c]
                                      (-> [(-> [[&t @c] [&t @c]] [&t @c])
                                           [&t (+ 1 $l) @c]]
                                          [&t @c])))))]
                     []
                     ((scl (λ [(v 1)] (sqrt (reduce + (* v v)))))
                      (array {0} []))
                     type env archive e:expr)
         archive))
  
  (test "vec+ -- recognize aliasing between argument dimensions"
        (judgment-holds
         (synth/expr [(+ (DR (-> [Int Int] Int)))]
                     []
                     (rerank [1 1] +)
                     type env archive e:expr)
         {type env archive e:expr}))
  
  (test "transpose+ -- instantiate polymorphic function, leading to dimension aliasing"
        (judgment-holds
         (synth/atom [(+ (DR (-> [Int Int] Int)))
                      (transpose (DR (∀ [&t] (Π [$m $n] (-> [[&t $m $n]] [&t $n $m])))))]
                     []
                     (λ [(x 2)] (+ x (transpose x)))
                     type env archive e:atom)
         {type env archive e:atom}))
  
  (test "1D stencil -- build iteration space, recognize its shape"
        (judgment-holds
         (synth/atom [(* (DR (-> [Int Int] Int)))
                      (+ (DR (-> [Int Int] Int)))
                      (iota/w (DR (∀ [&t0] (Π [@s] (-> [[&t0 @s]]
                                                       [Int @s])))))
                      (rotate (DR (∀ [&t1] (Π [$l1 @c1] (-> [[Int]
                                                             [&t1 $l1 @c1]]
                                                            [&t1 $l1 @c1])))))
                      (reduce/0 (DR (∀ [&t2] (Π [$l2 @c2]
                                               (-> [(-> [[&t2 @c2] [&t2 @c2]] [&t2 @c2])
                                                    [&t2 @c2]
                                                    [&t2 $l2 @c2]]
                                                   [&t2 @c2])))))]
                     []
                     (λ [(weights 1) (signal 1)]
                       (reduce/0 (rerank [1 1] +)
                                 ((scl (λ [(k 0)] (scl 0))) signal)
                                 (* weights (rotate (iota/w weights) signal))))
                     type env archive e:atom)
         {type env archive e:atom}))

  (test "1D stencil with \"liftable reduce\" -- add in lift-shape recognition"
        (judgment-holds
         (synth/atom [(* (DR (-> [Int Int] Int)))
                      (+ (DR (-> [Int Int] Int)))
                      (iota/w (DR (∀ [&t0] (Π [@s] (-> [[&t0 @s]]
                                                       [Int @s])))))
                      (rotate (DR (∀ [&t1] (Π [$l1 @c1] (-> [[Int]
                                                             [&t1 $l1 @c1]]
                                                            [&t1 $l1 @c1])))))
                      (reduce/L0 (DR (∀ [&t2] (Π [$l2 @f2 @c2]
                                                (-> [(-> [[&t2 @c2] [&t2 @c2]] [&t2 @c2])
                                                     [&t2 @c2]
                                                     [&t2 $l2 @f2 @c2]]
                                                    [&t2 @f2 @c2])))))]
                     []
                     (λ [(weights 1) (signal 1)]
                       (reduce/L0 + (array {} [0]) (* weights (rotate (iota/w weights) signal))))
                     type env archive e:atom)
         {type env archive e:atom}))

  (test "mtx* -- reranking, instantiation, dim aliasing, frame selection"
        (judgment-holds
         (synth/atom [(* (DR (-> [Int Int] Int)))
                      (+ (DR (-> [Int Int] Int)))
                      (reduce/L0 (DR (∀ [&t2] (Π [$l2 @f2 @c2]
                                                (-> [(-> [[&t2 @c2] [&t2 @c2]] [&t2 @c2])
                                                     [&t2 @c2]
                                                     [&t2 $l2 @f2 @c2]]
                                                    [&t2 @f2 @c2])))))]
                     []
                     (λ [(a 2) (b 2)]
                       ((rerank [0 0 2] reduce/L0)
                        + (scl 0)
                        ((rerank [1 2] *) a b)))
                     type env archive e:atom)
         {type env archive e:atom}))
  
  (test "poly/monomorphic functions coexisting -- instantiate sub-array"
        (judgment-holds
         (synth/expr [(+ (DR (-> [Int Int] Int)))
                      (fst (DR (∀ [&t]  (-> [&t &t] &t))))]
                     []
                     (frame {2} [+ fst])
                     type env archive e:expr)
         {type env archive e:expr}))

  (test "poly/monomorphic functions conflicting -- inference is still order-dependent"
        (judgment-holds
         (synth/expr [(+ (DR (-> [Int Int] Int)))
                      (fst (DR (∀ [&t]  (-> [&t &t] &t))))]
                     []
                     (frame {2} [fst +])
                     _ _ _ _)))
  
  (test "build and consume a box"
        (judgment-holds
         (synth/expr [(length (DR (∀ [&t] (Π [$l @c] (-> [[&t $l @c]] Int)))))]
                     []
                     ((scl
                       (λ [(x (Array (Σ [$d] (Array Int (Shp $d))) (Shp)))]
                         (unbox ($l v x) (length v))))
                      (scl (box 4 (array {4} [1 2 3 4]))))
                     type env archive e:expr)
         {type env archive e:expr}))

  (test "misuse of unboxing"
        (judgment-holds
         (synth/expr [(reverse (DR (∀ [&t] (Π [$l @c] (-> [[&t $l @c]] [&t $l @c])))))]
                     []
                     ((scl
                       (λ [(x (Array (Σ [$d] (Array Int (Shp $d))) (Shp)))]
                         (unbox ($l v x) (reverse v))))
                      (scl (box 4 (array {4} [1 2 3 4]))))
                     _ _ _ _)))

  (test "factorial -- unbox value made by primop"
        (judgment-holds
         (synth/atom [(+ (DR (-> [Int Int] Int)))
                      (* (DR (-> [Int Int] Int)))
                      (iota0 (DR (-> [Int] (Σ ($l) [Int $l]))))
                      (reduce/0 (DR (∀ [&t]
                                      (Π [$l @c]
                                        (-> [(-> [[&t @c] [&t @c]] [&t @c])
                                             [&t @c]
                                             [&t $l @c]]
                                            [&t @c])))))]
                     []
                     (λ [(x 0)]
                       (unbox ($l v (iota0 x))
                         (reduce/0 * (scl 0) (+ (scl 1) v))))
                     type env archive e:atom)
         {type env archive e:atom})))
