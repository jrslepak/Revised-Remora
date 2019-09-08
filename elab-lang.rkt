#lang racket

(require redex
         "implicit-lang.rkt"
         "language.rkt")

(provide Remora-explicit*
         Remora-implicit*
         Remora-elab)

;;; Define extended versions of implicit/explicit Remora which allow unsolved
;;; existential variables.
(define-extended-language Remora-implicit* Remora-implicit
  (exatmvar (^ atmvar))
  (atmtype .... exatmvar)
  (exarrvar (^ arrvar))
  (arrtype .... (^ arrvar))
  (exdvar (^ dvar))
  (dim .... exdvar)
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
