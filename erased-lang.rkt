#lang racket

(require redex
         "list-utils.rkt"
         "typing-rules.rkt")

(define-extended-language Remora-erased Remora-annotated
  (atom:e base-val
          op
          (λ (var ...) expr:e)
          (Iλ (var ...) val:e)
          (box idx ... expr:e type:e))
  (atval:e base-val
           op
           (λ (var ...) expr:e)
           (Iλ (var ...) val:e)
           (box idx ... val:e type:e))
  (expr:e var
          (array {natural ...} [atom:e ...])
          ;; A frame construct gets marked with its entire type, not just its
          ;; shape. When it's time to collapse the frame, code generated from a
          ;; well-typed program will always have the right number of cells, and
          ;; their shapes will always match.
          (frame type:e [expr:e ...])
          ;; Function application: this function array, applied to these
          ;; argument arrays, construed with these cell shapes, producing this
          ;; end result type.
          (expr:e (expr:e :: type:e) ... : type:e)
          (i-app expr:e idx ... : type:e)
          (unbox (var ... var expr:e) expr:e))
  (val:e var
         (array {natural ...} [atval:e ...]))
  (type:e flat
          (Σ [(var sort) ...] type:e)
          (Array type:e idx))
  (E:e hole
       (E:e (expr:e :: type:e) ... : type:e)
       (val:e (val:e :: type:e) ...
              (E:e :: type:e)
              (expr:e :: type:e) ...
              : type:e)
       ;(val:e ... E:e expr:e ... : type:e)
       (i-app E:e idx ...)
       (box idx ... E:e : type:e)
       (unbox (var_i ... var_e E:e) expr:e)
       (unbox (var_i ... var_e val:e) E:e)))

(define ->R:e
  (reduction-relation
   Remora-erased
   #:domain expr:e
   [==> ((array {} [(λ (var ...) expr:e)])
         (val:e :: (Array _ idx_cell)) ...
         : type:e)
        (subst* expr:e [(var (array {natural ...} [atval:e ...])) ...])
        (where [(array {natural ...} [atval:e ...]) ...] [val:e ...])
        (where #t (all [(idx=? {Shp natural ...} idx_cell) ...]))
        β]
   with
   [(--> (in-hole E:e a) (in-hole E:e b))
    (==> a b)]))

(define-metafunction Remora-erased
  erase-type : type -> type:e
  [(erase-type (Array type idx)) (Array (erase-type type) idx)]
  [(erase-type (Σ [(var sort) ...] type:e)) (Σ [(var sort) ...] (erase-type type))]
  [(erase-type (Π _ type)) (erase-type type)]
  [(erase-type (∀ _ type)) (erase-type type)]
  [(erase-type var) flat]
  [(erase-type (-> _ _)) flat]
  [(erase-type base-type) flat])

(define-metafunction Remora-erased
  erase-atom : atom:t -> atom:e
  [(erase-atom base-val) base-val]
  [(erase-atom op) op]
  [(erase-atom (λ [var ...] expr:t : (-> [type_in ...] type_out)))
   (λ [var ...] (erase-expr expr:t))]
  [(erase-atom (tλ [var ...] val:t : type))
   (erase-atom val:t)]
  [(erase-atom (iλ [var ...] val:t : type))
   (iλ [var ...] (erase-atom val:t))]
  [(erase-atom (box idx ... expr:t : type))
   (box idx ... (erase-expr expr:t) (erase-type type))])

(define-metafunction Remora-erased
  erase-expr : expr:t -> expr:e
  [(erase-expr (var : type)) var]
  [(erase-expr (array {natural ...} [atom:t ...] : type))
   (array {natural ...} [(erase-atom atom:t) ...])]
  [(erase-expr (frame {natural ...} [expr:t ...] : type))
   (frame (erase-type type) [(erase-expr expr:t) ...])]
  [(erase-expr (expr:t_f expr:t_a ... : type))
   ((erase-expr expr:t_f) [(erase-expr expr:t_a) :: (erase-type type_in)] ...
                          : (erase-type type))
   (where (_ ... : (Array (-> [type_in ...] _) _)) expr:t_f)]
  [(erase-expr (t-app expr:t_f type_a ... : type))
   (erase-expr expr:t_f)]
  [(erase-expr (i-app expr:t_f idx_a ... : type))
   (i-app (erase-expr expr:t_f) idx_a ... : (erase-type type))]
  [(erase-expr (unbox (var_i ... var_e expr:t_s) expr:t_b : type))
   (unbox (var_i ... var_e (erase-expr expr:t_s)) (erase-expr expr:t_b))])


(define-metafunction Remora-erased
    scl:e : atom:e -> expr:e
    [(scl:e atom:e) (array {} [atom:e])])
