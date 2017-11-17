#lang racket

(require redex
         "list-utils.rkt"
         "typing-rules.rkt")
(module+ test (require rackunit))

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
   ;; These rules pick apart shape annotations in a way that assumes they are
   ;; all normalized.
   [==> ((array {natural_f ...}
                [atval:e_f ...])
         ((array {natural_a ... natural_i ...}
                 [atval:e_a ...])
          :: (Array type:e_i {Shp natural_i ...})) ...
         : type:e_app)
        ((array {natural_p ...}
                (concat (replicate-each
                         (split [atval:e_f ...] (nprod {natural_f ...}))
                         natural_fe)))
         ((array {natural_p ... natural_i ...}
                 (concat (replicate-each
                          (split [atval:e_a ...] (nprod {natural_i ...}))
                          natural_ae)))
          :: (Array type:e_i {Shp natural_i ...})) ...
         : type:e_app)
        (where {Shp natural_p ...}
          (largest-frame [{Shp natural_f ...} {Shp natural_a ...} ...]))
        (side-condition
         (not (term (all [(idx=?
                           {Shp natural_p ...} {Shp natural_f ...})
                          (idx=?
                           {Shp natural_p ...} {Shp natural_a ...}) ...]))))
        (where [natural_fe natural_ae ...]
          [(nprod/s
            (drop-prefix {Shp natural_f ...} {Shp natural_p ...}))
           (nprod/s
            (drop-prefix {Shp natural_a ...} {Shp natural_p ...})) ...])
        lift]
   ;; Generating the new annotation on the individual cells' app forms requires
   ;; having already-normalized indices in the original annotations.
   [==> ((array {natural_f ...} [atval:e_f ...])
         ((array {natural_f0 ... natural_in ...} [atval:e_a ...])
          :: (Array type:e_in {Shp natural_in ...}))
         ...
         : (Array type:e_out idx_out))
        (frame
         (Array type:e_out idx_out)
         [((array {} [atval:e_f])
           ((array {natural_in ...}
                   [atval:e_cell ...])
            :: (Array type:e_in {Shp natural_in ...})) ...
           : (Array type:e_out (drop-prefix idx_frame idx_out))) ...])
        ;; Redex objects to having natural_f appear under two ellipses after
        ;; being bound under one, so wrap the one-ellipsis version up as a
        ;; single value.
        (where idx_frame {Shp natural_f ...})
        (where #t (all [(idx=? {Shp natural_f ...} {Shp natural_f0 ...}) ...]))
        (side-condition (< 0 (length (term {natural_f ...}))))
        (where (((atval:e_cell ...) ...) ...)
          (transpose/m ((split [atval:e_a ...] (nprod {natural_in ...})) ...)))
        map]
   [==> ((array {} [(λ (var ...) expr:e)])
         (val:e :: (Array _ idx_cell)) ...
         : type:e)
        ;; TODO: do shapes need to be normalized after substitution?
        (subst* expr:e [(var (array {natural ...} [atval:e ...])) ...])
        (where [(array {natural ...} [atval:e ...]) ...] [val:e ...])
        (where #t (all [(idx=? {Shp natural ...} idx_cell) ...]))
        β]
   [==> (i-app (array {natural_f ...} [(Iλ (var ...) val:e) ...])
               idx ... : type:e)
        ;; TODO: do shapes need to be normalized after substitution?
        (frame type:e [(subst* val:e [(var idx) ...]) ...])
        iβ]
   [==> (frame (Array type:e_c {Shp natural_fc ...})
               [(array _ [atval:e ...]) ...])
        (array {natural_fc ...} (concat ([atval:e ...] ...)))
        collapse]
   with
   [(--> (in-hole E:e a) (in-hole E:e b))
    (==> a b)]))

(module+ test
  (define (check-step now next)
    (check-equal? (apply-reduction-relation ->R:e now) (list next)))
  ;; Test for lift step
  (check-step
   (term
    ((array {2} [(λ (x) x) (λ (x) x)])
     ((array {2 3} [1 2 3 4 5 6]) :: (Array flat {Shp}))
     : (Array flat {Shp 2 3})))
   (term
    ((array {2 3} [(λ (x) x)
                   (λ (x) x)
                   (λ (x) x)
                   (λ (x) x)
                   (λ (x) x)
                   (λ (x) x)])
     ((array {2 3} [1 2 3 4 5 6]) :: (Array flat {Shp}))
     : (Array flat {Shp 2 3}))))
  ;; Test for map step
  (check-step
   (term
    ((array {2} [(λ (x) x) (λ (x) x)])
     ((array {2 3} [1 2 3 4 5 6]) :: (Array flat {Shp 3}))
     : (Array flat {Shp 2 3})))
   (term (frame (Array flat {Shp 2 3})
                [((scl:e (λ (x) x))
                  ((array {3} [1 2 3]) :: (Array flat {Shp 3}))
                  : (Array flat {Shp 3}))
                 ((scl:e (λ (x) x))
                  ((array {3} [4 5 6]) :: (Array flat {Shp 3}))
                  : (Array flat {Shp 3}))])))
  ;; Test for β step
  (check-step
   (term ((scl:e (λ (xs) ((scl:e +)
                          ((scl:e 1) :: (Array flat {Shp}))
                          (xs :: (Array flat {Shp}))
                          : (Array flat {Shp 4}))))
          ((array {4} [2 3 5 7]) :: (Array flat {Shp 4}))
          : (Array flat {Shp 4})))
   (term ((scl:e +)
          ((scl:e 1) :: (Array flat {Shp}))
          ((array {4} [2 3 5 7]) :: (Array flat {Shp}))
          : (Array flat {Shp 4}))))
  ;; Test for iβ step
  (check-step
   (term (i-app
          (scl:e
           (Iλ (shp len)
             (scl:e
              (λ ()
                (i-app (array {} [iota]) (++ {Shp len} shp)
                       : (Array flat (++ {Shp len} shp)))))))
          {Shp 2 3} 5
          : (Array flat (++ len shp))))
   (term
    (frame
     (Array flat (++ len shp))
     [(scl:e
       (λ ()
         (i-app (array {} [iota]) (++ {Shp 5} {Shp 2 3})
                : (Array flat (++ {Shp 5} {Shp 2 3})))))])))

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
