#lang racket

(require redex
         "language.rkt"
         "list-utils.rkt"
         "typing-rules.rkt")
(module+ test (require rackunit))

(define-extended-language Remora-erased Remora-annotated
  (atom:e base-val
          op
          (λ (var ...) expr:e)
          (Iλ (var ...) val:e)
          (box idx ... expr:e))
  (atval:e base-val
           op
           (λ (var ...) expr:e)
           (Iλ (var ...) val:e)
           (box idx ... val:e))
  (expr:e var
          (array {natural ...} [atom:e ...])
          ;; A frame construct gets marked with its entire type, not just its
          ;; shape. When it's time to collapse the frame, code generated from a
          ;; well-typed program will always have the right number of cells, and
          ;; their shapes will always match.
          (frame idx [expr:e ...])
          ;; Function application: this function array, applied to these
          ;; argument arrays, construed with these cell shapes, producing this
          ;; end result type.
          (expr:e (expr:e :: idx) ... : idx)
          (i-app expr:e idx ... : idx)
          (unbox (var ... var expr:e) expr:e))
  (val:e var
         (array {natural ...} [atval:e ...]))
  (type:e flat
          (Σ (var ...) type:e)
          (Array type:e idx))
  (E:e hole
       (E:e (expr:e :: idx) ... : idx)
       (val:e (val:e :: idx) ...
              (E:e :: idx)
              (expr:e :: idx) ...
              : idx)
       ;(val:e ... E:e expr:e ... : idx)
       (i-app E:e idx ...)
       (box idx ... E:e)
       (unbox (var_i ... var_e E:e) expr:e)))

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
          :: {Shp natural_i ...}) ...
         : idx_app)
        ((array {natural_p ...}
                (concat (replicate-each
                         (split [atval:e_f ...] (nprod {natural_f ...}))
                         natural_fe)))
         ((array {natural_p ... natural_i ...}
                 (concat (replicate-each
                          (split [atval:e_a ...] (nprod {natural_i ...}))
                          natural_ae)))
          :: {Shp natural_i ...}) ...
         : idx_app)
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
          :: {Shp natural_in ...})
         ...
         : idx_out)
        (frame
         idx_frame
         [((array {} [atval:e_f])
           ((array {natural_in ...}
                   [atval:e_cell ...])
            :: {Shp natural_in ...}) ...
           : (drop-prefix idx_frame idx_out)) ...])
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
         (val:e :: idx_cell) ...
         : idx)
        ;; TODO: do shapes need to be normalized after substitution?
        (subst* expr:e [(var (array {natural ...} [atval:e ...])) ...])
        (where [(array {natural ...} [atval:e ...]) ...] [val:e ...])
        (where #t (all [(idx=? {Shp natural ...} idx_cell) ...]))
        β]
   [==> (i-app (array {natural_f ...} [(Iλ (var ...) val:e) ...])
               idx_a ... : idx_f)
        ;; TODO: do shapes need to be normalized after substitution?
        (frame idx_f [(subst* val:e [(var idx_a) ...]) ...])
        iβ]
   [==> (frame {Shp natural_fc ...}
               [(array _ [atval:e ...]) ...])
        (array {natural_fc ...} (concat ([atval:e ...] ...)))
        collapse]
   [==> (unbox (var_i ... var_e (array {} [(box idx ... val:e)]))
          expr:e)
        (subst* (substitute expr:e var_e val:e)
                [(var_i idx) ...])
        let-box]
   with
   [(--> (in-hole E:e a) (in-hole E:e b))
    (==> a b)]))

(module+ test
  (define-syntax-rule (check-step now next)
    (check-equal? (apply-reduction-relation ->R:e now) (list next)))
  ;; Test for lift step
  (check-step
   (term
    ((array {2} [(λ (x) x) (λ (x) x)])
     ((array {2 3} [1 2 3 4 5 6]) :: {Shp})
     : {Shp 2 3}))
   (term
    ((array {2 3} [(λ (x) x)
                   (λ (x) x)
                   (λ (x) x)
                   (λ (x) x)
                   (λ (x) x)
                   (λ (x) x)])
     ((array {2 3} [1 2 3 4 5 6]) :: {Shp})
     : {Shp 2 3})))
  ;; Test for map step
  (check-step
   (term
    ((array {2} [(λ (x) x) (λ (x) x)])
     ((array {2 3} [1 2 3 4 5 6]) :: {Shp 3})
     : {Shp 2 3}))
   (term (frame {Shp 2}
                [((scl:e (λ (x) x))
                  ((array {3} [1 2 3]) :: {Shp 3})
                  : {Shp 3})
                 ((scl:e (λ (x) x))
                  ((array {3} [4 5 6]) :: {Shp 3})
                  : {Shp 3})])))
  ;; Test for β step
  (check-step
   (term ((scl:e (λ (xs) ((scl:e %+)
                          ((scl:e 1) :: {Shp})
                          (xs :: {Shp})
                          : {Shp 4})))
          ((array {4} [2 3 5 7]) :: {Shp 4})
          : {Shp 4}))
   (term ((scl:e %+)
          ((scl:e 1) :: {Shp})
          ((array {4} [2 3 5 7]) :: {Shp})
          : {Shp 4})))
  ;; Test for iβ step
  (check-step
   (term (i-app
          (scl:e
           (Iλ (shp len)
             (scl:e
              (λ ()
                (i-app (array {} [%iota]) {++ {Shp len} shp}
                       : {++ {Shp len} shp})))))
          {Shp 2 3} 5
          : {++ len shp}))
   (term
    (frame
     {++ len shp}
     [(scl:e
       (λ ()
         (i-app (array {} [%iota]) {++ {Shp 5} {Shp 2 3}}
                : {++ {Shp 5} {Shp 2 3}})))])))
  ;; Test for collapse step
  (check-step
   (term (frame {Shp 2 3}
                [(array {3} [10 20 30])
                 (array {3} [40 50 60])]))
   (term (array {2 3} [10 20 30 40 50 60])))
  ;; Test for collapse step, with an empty frame
  (check-step
   (term (frame {Shp 2 0 3} []))
   (term (array {2 0 3} [])))
  ;; Test for let-box step
  (check-step
   (term (unbox (z m (scl:e (box 3 (array {3 3} [1 2 3 4 5 6 7 8 9]))))
           ((i-app (scl:e %length) z {Shp z} : {Shp})
            (m :: {Shp 3 3})
            : {Shp})))
   (term ((i-app (scl:e %length) 3 {Shp 3} : {Shp})
          ((array {3 3} [1 2 3 4 5 6 7 8 9])
           :: {Shp 3 3})
          : {Shp}))))

(define-metafunction Remora-erased
  erase-type : type -> idx
  [(erase-type var) var]
  [(erase-type (Array type idx)) (normalize-idx {++ (erase-type type) idx})]
  [(erase-type (∀ _ type)) {Shp}]
  [(erase-type (Σ _ _)) {Shp}]
  [(erase-type (Π _ _)) {Shp}]
  [(erase-type (-> _ _)) {Shp}]
  [(erase-type base-type) {Shp}])

(define-metafunction Remora-erased
  erase-atom : atom:t -> atom:e
  [(erase-atom base-val) base-val]
  [(erase-atom op) op]
  [(erase-atom (λ [var ...] expr:t : (-> [type_in ...] type_out)))
   (λ [var ...] (erase-expr expr:t))]
  [(erase-atom (iλ [var ...] val:t : type))
   (iλ [var ...] (erase-atom val:t))]
  ;; Type abstractions become index abstractions, which only bind the index
  ;; information carried by what was originally a type argument.
  [(erase-atom (tλ [var ...] val:t : type))
   (iλ [var ...] (erase-atom val:t))]
  [(erase-atom (box idx ... expr:t : type))
   (box idx ... (erase-expr expr:t))])

(define-metafunction Remora-erased
  erase-expr : expr:t -> expr:e
  [(erase-expr (var : type)) var]
  [(erase-expr (array {natural ...} [atom:t ...] : type_r))
   (array {natural ...} [(erase-atom atom:t) ...])]
  [(erase-expr (frame {natural ...} [expr:t ...] : type_r))
   (frame (erase-type type) [(erase-expr expr:t) ...])]
  [(erase-expr (expr:t_f expr:t_a ... : type_r))
   ((erase-expr expr:t_f) [(erase-expr expr:t_a) :: (erase-type type_in)] ...
                          : (erase-type type_r))
   (where (_ ... : (Array (-> [type_in ...] _) _)) expr:t_f)]
  ;; Corresponding to the conversion of type abstractions to index abstractions,
  ;; type application passes only the index information a type contains.
  [(erase-expr (t-app expr:t_f type_a ... : type_r))
   (i-app (erase-expr expr:t_f) (erase-type type_a) ... : (erase-type type_r))]
  [(erase-expr (i-app expr:t_f idx_a ... : type_r))
   (i-app (erase-expr expr:t_f) idx_a ... : (erase-type type_r))]
  [(erase-expr (unbox (var_i ... var_e expr:t_s) expr:t_b : type_r))
   (unbox (var_i ... var_e (erase-expr expr:t_s)) (erase-expr expr:t_b))])


(define-metafunction Remora-erased
    scl:e : atom:e -> expr:e
    [(scl:e atom:e) (array {} [atom:e])])
