#lang racket

(require redex
         "language.rkt"
         "typing-rules.rkt")

(module+ test
  (require rackunit))

(define-extended-language Remora-exec Remora-annotated
  (E hole
     (E expr:t)
     (val:t E)
     (TApp E type)
     (IApp E idx)
     (Box idx E)
     (Unbox (var var E) expr:t)
     (Unbox (var var val:t) E)))

(define ->R
  (reduction-relation
   Remora-exec
   #:domain expr:t
   ;; Redex forms:
   ;; - (op val)
   ;; - ((λ ___) val)
   ;; - (TApp (Tλ ___) type)
   ;; - (TApp (Arr (val ...) __)) type)
   (==> (TApp (Arr [scal:t ...] {natural ...}
                              : ((∀ var type_univ) idx_shp)) type_arg
                                                             : type_tapp)
        (Arr [(TApp scal:t type_arg
                               : (substitute type_univ var type_arg)) ...]
                        {natural ...}
                        : type_tapp)
        TMap)
   ;; - (IApp (Iλ ___) idx)
   ;; - (IApp (Arr ((Iλ ___) ...) __)) type)
   ;; - (Unbox (___ (Box)) ___)
   ;; - (Arr ((Arr ___) ...) ___)
   with
   [(--> (in-hole E a) (in-hole E b))
    (==> a b)]))

(module+ test
  (check-equal? (apply-reduction-relation
                 ->R
                 (term (TApp (Arr [(x : (&∀ [t] (&-> [t] t)))
                                   (y : (&∀ [t] (&-> [t] t)))
                                   (z : (&∀ [t] (&-> [t] t)))] {3} : ((∀ t (&-> [t] t)) {Shp 3}))
                             Int : ((Int -> Int) {Shp 3}))))
                (list (term (Arr [(TApp (x : (&∀ [t] (&-> [t] t))) Int : (&-> [Int] Int))
                                  (TApp (y : (&∀ [t] (&-> [t] t))) Int : (&-> [Int] Int))
                                  (TApp (z : (&∀ [t] (&-> [t] t))) Int : (&-> [Int] Int))] {3}
                                 : ((Int -> Int) {Shp 3}))))))
