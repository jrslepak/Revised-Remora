#lang racket

(require redex
         "elab-lang.rkt")
(provide kind-atm kind-array
         sort-dim sort-shp)

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
