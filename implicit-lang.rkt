#lang racket

(require redex)
(provide Remora-implicit
         IScl Iscl I&-> I&Π I&Σ I&∀ I&
         op->Itype
         rerank
         #;Inormalize-idx)

(define-language Remora-implicit
  (var + - * and or not > < =
       length shape reduce iota reshape
       variable-not-otherwise-mentioned)
  (evar var #;(variable-prefix ?))
  ;; Several classes of vars, which effectively carry their kind/sort
  (dvar (variable-prefix $))
  (svar (variable-prefix @))
  (ivar dvar svar)
  (atmvar (variable-prefix &))
  (arrvar (variable-prefix *))
  (tvar atmvar arrvar)
  ;; Term level
  (atom base-val
        op
        (λ [(evar spec) ...] expr)
        (box idx ... expr)
        (atom : type))
  (base-val integer boolean)
  (expr evar
        (array {natural ...} [atom ...])
        (frame {natural ...} [expr ...])
        (expr expr ...)
        (unbox (ivar ... evar expr) expr)
        (expr : type))
  (AE atom expr)
  (spec rank type)
  (rank natural all)
  (op %+ %- %* %and %or %not %> %< %=
      %length %shape %reduce %iota %reshape)
  ;; Type level
  (atmtype atmvar
           base-type
           (-> [arrtype ...] arrtype)
           (∀ [tvar ...] arrtype)
           (Π [ivar ...] arrtype)
           (Σ [ivar ...] arrtype))
  ;; TODO: Should type vars be allowed to stand for Π/Σ types?
  (atmmono atmvar base-type (-> [arrtype ...] arrtype))
  (arrtype arrvar
           (Array atmtype shp))
  (arrmono arrvar (Array atmmono shp))
  (type atmtype arrtype)
  (monotype atmmono arrmono)
  (base-type Int Bool)
  (kind Array Atom)
  ;; Index level
  (dim dvar natural {+ dim ...})        ; any dimension
  (ndim adim {+ adim adim ...+})        ; normalized dimension
  (adim dvar natural)                   ; atomic dimensions
  (shp svar {Shp dim ...} {++ shp ...}) ; any shape
  (nshp fshp {++ fshp fshp ...+} {Shp}) ; normalized shape
  (fshp svar {Shp ndim ndim ...+})      ; flat shape
  (idx dim shp)                         ; any index
  (nidx ndim nshp)                      ; normalized index
  (sort Dim Shape)
  ;; Type inference environment structure
  (env (env-entry ...))
  (env-entry (evar arrtype)
             ;; Universal var, unsolved existential var, solved existential var
             tvar (^ tvar) (^ tvar type)
             ivar (^ ivar) (^ ivar idx)
             ;; Scope marker
             (?i var))
  ;; Archive of facts discovered about exvars (used like environment, but don't
  ;; delete things right when exvars go out of scope)
  (archive (archive-entry ...))
  (archive-entry (≐ dim dim ...+)
                 (^ tvar) (^ tvar type)
                 (^ ivar) (^ tvar idx))
  #:binding-forms
  (expr #:refers-to type : type)
  (atom #:refers-to type : type)
  (λ [(evar spec) ...] expr #:refers-to (shadow evar ...))
  (unbox (ivar ... evar expr) expr #:refers-to (shadow ivar ... evar))
  (∀ [tvar ...] type #:refers-to (shadow tvar ...)) #:exports (shadow tvar ...)
  (Π [ivar ...] type #:refers-to (shadow ivar ...)) #:exports (shadow ivar ...)
  (Σ [ivar ...] type #:refers-to (shadow ivar ...)) #:exports (shadow ivar ...))

;;; Build a scalar expr from any atom
(define-metafunction Remora-implicit
  Iscl : atom -> expr
  [(Iscl atom) (array {} [atom])])
;;; Build an Array type from any Atom type
(define-metafunction Remora-implicit
    IScl : atmtype -> arrtype
    [(IScl type) (Array type {Shp})])

;;; Utilities for inserting `scalar' calls where needed.
(define-metafunction Remora-implicit
  I&-> : [type ...] type -> type
  [(I&-> [type_in ...] type_out)
   (IScl (-> [(I& type_in) ...] (I& type_out)))])
(define-metafunction Remora-implicit
  I&Π : [ivar ...] type -> type
  [(I&Π (ivar ...) type)
   (Π (ivar ...) (I& type))])
(define-metafunction Remora-implicit
  I&Σ : [ivar ...] type -> type
  [(I&Σ (ivar ...) type)
   (Σ (ivar ...) (I& type))])
(define-metafunction Remora-implicit
  I&∀ : [tvar ...] type -> type
  [(I&∀ [tvar ...] type)
   (∀ [tvar ...] (I& type))])
(define-metafunction Remora-implicit
  I& : type -> type
  [(I& (Array type idx)) (Array type idx)]
  [(I& (-> [type_in ...] type_out))
   (I&-> [type_in ...] type_out)]
  [(I& var) (IScl var)]
  [(I& base-type) (IScl base-type)]
  [(I& (∀ [tvar ...] type))
   (IScl (I&∀ [tvar ...] type))]
  [(I& (Π any ...))
   (IScl (I&Π any ...))]
  [(I& (Σ [ivar ...] type))
   (IScl (I&Σ [ivar ...] type))])

(define-metafunction Remora-implicit
  op->Itype : op -> type
  [(op->Itype %+) (-> [(IScl Int) (IScl Int)] (IScl Int))]
  [(op->Itype %-) (-> [(IScl Int) (IScl Int)] (IScl Int))]
  [(op->Itype %*) (-> [(IScl Int) (IScl Int)] (IScl Int))]
  [(op->Itype %and) (-> [(IScl Bool) (IScl Bool)] (IScl Bool))]
  [(op->Itype %or) (-> [(IScl Bool) (IScl Bool)] (IScl Bool))]
  [(op->Itype %not) (-> [(IScl Bool)] (IScl Bool))]
  [(op->Itype %<) (-> [(IScl Int) (IScl Int)] (IScl Bool))]
  [(op->Itype %=) (-> [(IScl Int) (IScl Int)] (IScl Bool))]
  [(op->Itype %>) (-> [(IScl Int) (IScl Int)] (IScl Bool))]
  [(op->Itype %length) (∀ [&t]
                         (IScl
                          (Π [$l @s]
                            (IScl
                             (-> [(Array &t {++ {Shp $l} @s})] (IScl Int))))))]
  [(op->Itype %shape) (∀ [&t]
                        (IScl
                         (Π [@s]
                           (IScl
                            (-> [(Array &t @s)]
                                (IScl (Σ [$r] (Array Int {Shp $r}))))))))]
  [(op->Itype %reduce) (∀ [&t]
                         (IScl
                          (I&Π [$l @f @c]
                               (I&-> [(I&-> [(Array &t @c) (Array &t @c)]
                                            (Array &t @c))
                                      (Array &t {++ @f @c})
                                      (Array &t {++ {Shp $l} @f @c})]
                                     (Array &t {++ @f @c})))))]
  [(op->Itype %iota) (Π [$r]
                       (IScl (-> [(Array Int {Shp $r})]
                                 (IScl (Σ [@s] (Array Int @s))))))]
  [(op->Itype %reshape) (∀ [&t]
                          (IScl
                           (I&Π [$r @old]
                                (I&-> [(Array Int {Shp $r}) (Array &t @old)]
                                      (I&Σ [@new] (Array &t @new))))))])

(define-metafunction Remora-implicit
  rerank : [spec ...] expr -> expr
  [(rerank [spec ...] expr)
   (array {} [(λ [(var_fresh spec) ...] (expr var_fresh ...))])
   (where [var_fresh ...]
     ,(build-list (length (term (spec ...))) (λ _ (gensym 'RR_))))])
