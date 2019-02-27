#lang racket

(require redex
         "implicit-lang.rkt"
         "language.rkt")

;;; We need a single language which includes implicitly typed Remora and
;;; explicitly typed Remora because a Redex judgment-form is tied to a
;;; single Redex language. For elaboration, we want input in one language
;;; and output in another.
(define-union-language Remora-elab Remora-implicit (e: Remora-explicit))

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
  #:mode (synth/atom I I O O O)
  #:contract (synth/atom env atom atmtype env e:atom)
  ;; TODO: syn-fn (optional)
  [(check/atom env_0 atom atmtype env_1 e:atom)
   --- syn-annot
   (synth/atom env_0 (atom : atmtype) atmtype env_1 e:atom)]
  [(synth/atom env integer Int env integer)
   syn-int]
  [(synth/atom env boolean Bool env boolean)
   syn-bool]
  [(synth/atom env op (op->Itype op) env op)
   syn-op])

(define-judgment-form Remora-elab
  #:mode (synth/expr I I O O O)
  #:contract (synth/expr env expr arrtype env e:expr)
  ;; TODO: syn-app (will need synthapp judgment)
  [(synth/expr [env-entry_0 ...]
               expr_s
               ;; TODO: subtyping to reconcile possible exvar with need for Σ
               (Σ [ivar_s ...] arrtype_s)
               [env-entry_1 ...]
               e:expr_s)
   ;; The unbox arity tells how many Σ-bound ivars to demand
   (side-condition ,(= (length (term (ivar ...)) (term (ivar_s ...)))))
   (synth/expr [env-entry_1 ...
                ivar ...
                (evar : (subst* arrtype_s [(ivar_s ivar) ...]))]
               expr_b
               arrtype_b
               [env-entry_n ...
                ivar ... (evar : _)
                _ ...]
               e:expr_b)
   --- syn-unbox
   (synth/expr [env-entry_0 ...]
               (unbox (ivar ... evar expr_s) expr_b)
               arrtype_b
               [env-entry_n ...]
               (unbox (ivar ... evar e:expr_s) e:expr_b))]
  [(check/expr env_0 expr arrtype env_1 e:expr)
   --- syn-annot
   (synth/expr env_0 (expr : arrtype) arrtype env_1 e:expr)]
  [(where (_ ... (evar arrtype) _ ...) env)
   --- syn-var
   (synth/expr env evar arrtype env evar)]
  [(synth/atoms env_0 (atom ...) atmtype env_1 [e:atom ...])
   --- syn-array
   (synth/expr env_0
               (array {natural ...} [atom ...])
               (Array atmtype {Shp natural ...})
               env_1
               (array {natural ...} [e:atom ...]))]
  [(synth/exprs env_0 (expr ...) (Array atmtype shp) env_1 [e:expr ...])
   (side-condition ,(= (apply * (term (natural ...)))
                       (length (term (expr ...)))))
   --- syn-frame
   (synth/expr env_0
               (frame {natural ...} [expr ...])
               (Array atmtype
                      (Inormalize-idx {++ {Shp natural ...} shp}))
               env_1
               (frame {natural ...} [e:expr ...]))])


(define-judgment-form Remora-elab
  #:mode (check/atom I I I O O)
  #:contract (check/atom env atom atmtype env e:atom)
  ;; TODO: chk-sub, chk-fn, chk-box
  [(synth/atom env_0 atom atmtype env_1 e:atom)
   --- REPLACE-WITH-SUBTYPE-RULE
   (check/atom env_0 atom atmtype env_1 e:atom)])

(define-judgment-form Remora-elab
  #:mode (check/expr I I I O O)
  #:contract (check/expr env expr arrtype env e:expr)
  ;; TODO: chk-sub
  [(synth/expr env_0 expr arrtype env_1 e:expr)
   --- REPLACE-WITH-SUBTYPE-RULE
   (check/expr env_0 expr arrtype env_1 e:expr)]
  [(check/atoms env_0 [atom ...] atmtype env_1 [e:atom ...])
   (side-condition ,(= (apply * (term (natural ...)))
                       (length (term (atom ...)))))
   --- chk-array
   (check/expr env_0
               (array {natural ...} [atom ...])
               (Array atmtype
                      ;; TODO: use solver query to be more permissive
                      (Shp natural ...))
               env_1
               (array {natural ...} [e:atom ...]))])


;;;;----------------------------------------------------------------------------
;;;; Helper judgments for typing lists of terms all at the same type
;;;;----------------------------------------------------------------------------
(define-judgment-form Remora-elab
  #:mode (synth/atoms I I O O O)
  #:contract (synth/atoms env [atom ...+] atmtype env [e:atom ...+])
  [(synth/atom env_0 atom atmtype env_1 e:atom)
   --- syn*-base
   (synth/atoms env_0 [atom] atmtype env_1 [e:atom])]
  [(synth/atom env_0 atom_0 atmtype_join env_1 e:atom_0)
   (synth/atoms env_1 [atom_1 ...] atmtype_join env_n [e:atom_1 ...])
   ;; TODO: replace with join operation on types with exvars
   --- syn*
   (synth/atoms env_0 [atom_0 atom_1 ...+] atmtype_join
                env_n [e:atom_0 e:atom_1 ...])])

(define-judgment-form Remora-elab
  #:mode (synth/exprs I I O O O)
  #:contract (synth/exprs env [expr ...+] arrtype env [e:expr ...+])
  [(synth/expr env_0 expr arrtype env_1 e:expr)
   --- syn*-base
   (synth/exprs env_0 [expr] arrtype env_1 [e:expr])]
  [(synth/expr env_0 expr_0 arrtype_join env_1 e:expr_0)
   (synth/exprs env_1 [expr_1 ...] arrtype_join env_n [e:expr_1 ...])
   ;; TODO: replace with join operation on types with exvars
   --- syn*
   (synth/exprs env_0 [expr_0 expr_1 ...+] arrtype_join
                env_n [e:expr_0 e:expr_1 ...])])

(define-judgment-form Remora-elab
  #:mode (check/atoms I I I O O)
  #:contract (check/atoms env [atom ...] atmtype env [e:atom ...])
  [(check/atoms env [] _ env [])
   chk*-base]
  [(check/atom env_0 atom_0 atmtype env_1 e:atom_0)
   (check/atoms env_1 [atom_1 ...] atmtype env_n [e:atom_1 ...])
   --- chk*
   (check/atoms env_0 [atom_0 atom_1 ...] atmtype
                env_n [e:atom_0 e:atom_1 ...])])


(define-judgment-form Remora-elab
  #:mode (check/exprs I I I O O)
  #:contract (check/exprs env [expr ...] arrtype env [e:expr ...])
  [(check/exprs env [] _ env [])
   chk*-base]
  [(check/expr env_0 expr_0 arrtype env_1 e:expr_0)
   (check/exprs env_1 [expr_1 ...] arrtype env_n [e:expr_1 ...])
   --- chk*
   (check/exprs env_0 [expr_0 expr_1 ...] arrtype
                env_n [e:expr_0 e:expr_1 ...])])

;;;;----------------------------------------------------------------------------
;;;; Utility metafunction for multiple substitution
;;;;----------------------------------------------------------------------------
(define-metafunction Remora-elab
  subst* : any [(var any) ...] -> any
  [(subst* any []) any]
  [(subst* any_orig [(var any_new) any_subs ...])
   (subst* (substitute any_orig var any_new) [any_subs ...])])
