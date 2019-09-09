#lang racket

(require redex
         "language.rkt"
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
   --- syn-annot
   (synth/atom env_0 archive_0
               (atom : atmtype) atmtype
               env_1 archive_1 e:atom)]
  [(synth/atom env archive integer Int env archive integer)
   syn-int]
  [(synth/atom env archive boolean Bool env archive boolean)
   syn-bool]
  [(synth/atom env archive op (op->Itype op) env archive op)
   syn-op])

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
   --- syn-unbox
   (synth/expr [env-entry_0 ...]
               archive_0
               (unbox (ivar ... evar expr_s) expr_b)
               arrtype_b
               [env-entry_n ...]
               archive_2
               (unbox (ivar ... evar e:expr_s) e:expr_b))]
  [(check/expr env_0 archive_0 expr arrtype env_1 archive_1 e:expr)
   --- syn-annot
   (synth/expr env_0 archive_0 (expr : arrtype) arrtype env_1 archive_1 e:expr)]
  [(where (_ ... (evar arrtype) _ ...) env)
   --- syn-var
   (synth/expr env archive evar arrtype env archive evar)]
  [(synth/atoms env_0 archive_0
                (atom ...) atmtype
                env_1 archive_1 [e:atom ...])
   --- syn-array
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
   --- syn-frame
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
   --- chk-array
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
   sub-base])
(define-judgment-form Remora-elab
  #:mode (subtype/expr I I I I O O O)
  ;; TODO: Is syntactic context too general? maybe just T-App/I-App coercions?
  #:contract (subtype/expr env archive arrtype arrtype env archive e:ectx)
  [;; TODO: check whether shapes are equalizable instead of just being
   ;; syntactically equal after normalization
   (side-condition ,(equal? (term (Inormalize-idx shp_0))
                            (term (Inormalize-idx shp_1))))
   --- sub-exvar
   (subtype/expr
    env archive
    (Array base-type shp_0)
    (Array base-type shp_1)
    env archive
    hole)]
  [(equate env_0 archive_0 shp_0 shp_1 env_1 archive_1)
   --- sub-base
   (subtype/expr
    env_0 archive_0
    (Array base-type shp_0)
    (Array base-type shp_1)
    env_1 archive_1
    hole)]
  [;; TODO: check whether shapes are equalizable instead of just being
   ;; syntactically equal after normalization
   (side-condition ,(equal? (term (Inormalize-idx shp_0))
                            (term (Inormalize-idx shp_1))))
   --- sub-atmvar
   (subtype/expr
    env archive
    (Array atmvar shp_0)
    (Array atmvar shp_1)
    env archive
    hole)]
  [(subtype/expr env archive arrvar arrvar env archive hole)
   sub-arrvar]
  [(where var_sm ,(gensym 'SM_)) ; Generate a fresh scope-marking variable
   (subtype/atom
    [env-entry_0 ... (?i var_sm) (^ tvar) ...] archive_0
    (subst* atmtype_0 [(tvar (^ tvar)) ...])
    atmtype_1
    env_1 archive_1
    actx)
   --- sub-forallL
   (subtype/expr
    [env-entry_0 ...] archive_0
    (Array (∀ [tvar ...] atmtype_0) shp_0)
    (Array atmtype_1 shp_1)
    env_1 archive_1
    ?)]
  ;; As a "last resort" rule, we can conclude [T_1 S_1] <: [T_2 S_2] by making
  ;; sure T_1 <: T_2 and S_1 ≐ S_2. The resulting coercion will be ugly. It must
  ;; apply an η-expanded version of the atom coercion.
  ;; TODO: Is this ever actually needed?
  [(subtype/atom env_0 archive_0 atmtype_0 atmtype_1 env_1 archive_1 e:actx)
   (equate env_1 archive_1 shp_0 shp_1 env_2 archive_2)
   (where var_f ,(gensym 'coerce))
   --- sub-array
   (subtype/expr env_0 archive_0
                 (Array atmtype_0 shp_0)
                 (Array atmtype_1 shp_1)
                 env_2 archive_2
                 ((scl (λ [(coerce (Scl atmtype_0))] (in-hole e:actx coerce)))
                  hole))])

;;; Provide a judgment-form version of the logic used to interpret the solver's
;;; results
(define-judgment-form Remora-elab
  #:mode (equate I I I I O O)
  #:contract (equate env archive idx idx env archive)
  ;; Ask an ILP solver whether dim_0 and dim_1 can be equated and what values
  ;; must be assigned to their unsolved existential variables in order to do so.
  [(where (_ ... (env_1 archive_1) _ ...)
     (equate-shapes env_0 archive_0 shp_0 shp_1))
   --- equate-shp
   (equate env_0 archive_0 shp_0 shp_1 env_1 archive_1)]
  [--- equate-dim
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
   --- syn*-base
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
   --- syn*-base
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
  [(check/atoms env archive [] _ env archive [])
   chk*-base]
  [(check/atom env_0 archive_0 atom_0 atmtype env_1 archive_1 e:atom_0)
   (check/atoms env_1 archive_1 [atom_1 ...] atmtype env_n archive_n [e:atom_1 ...])
   --- chk*
   (check/atoms env_0 archive_0 [atom_0 atom_1 ...] atmtype
                env_n archive_n [e:atom_0 e:atom_1 ...])])


(define-judgment-form Remora-elab
  #:mode (check/exprs I I I I O O O)
  #:contract (check/exprs env archive [expr ...] arrtype env archive [e:expr ...])
  [(check/exprs env archive [] _ env archive [])
   chk*-base]
  [(check/expr env_0 archive_0 expr_0 arrtype env_1 archive_1 e:expr_0)
   (check/exprs env_1 archive_1 [expr_1 ...] arrtype env_n archive_n [e:expr_1 ...])
   --- chk*
   (check/exprs env_0 archive_0 [expr_0 expr_1 ...] arrtype
                env_n archive_n [e:expr_0 e:expr_1 ...])])

;;;;----------------------------------------------------------------------------
;;;; Utility metafunction for multiple substitution
;;;;----------------------------------------------------------------------------
(define-metafunction Remora-elab
  subst* : any [(var any) ...] -> any
  [(subst* any []) any]
  [(subst* any_orig [(var any_new) any_subs ...])
   (subst* (substitute any_orig var any_new) [any_subs ...])])
