#lang racket

;;; TODO: test case for non-valid formula
;;; TODO: better watching for Inez's failures (like from a bad script)

(provide (contract-out [inez-valid? (-> (listof cform?) cform?
                                        boolean?)]))

(module+ test (require redex rackunit))

(define (debug-ret str val . others)
  (begin #;(apply printf str val others)
         val))

;;;;----------------------------------------------------------------------------
;;;;
;;;;  Syntactic representation of constraint formulas/terms
;;;;
;;;;----------------------------------------------------------------------------

;;; A constraint formula ("cform") is one of
;;; - (list 'AND cform cform)
;;; - (list 'NOT cform)
;;; - (list cterm '≐ cterm)
;;; - (list cterm ≤ cterm)
(define/match (cform? x)
  [((list 'AND (? cform? _) (? cform? _))) #t]
  [((list 'NOT (? cform? _))) #t]
  [((list (? cterm? _) '≐ (? cterm? _))) #t]
  [((list (? cterm? _) '≤ (? cterm? _))) #t]
  [((list (? flattened-cterm? _) '≐ (? flattened-cterm? _))) #t]
  [(_) #f])

;;; A constraint term ("cterm") is one of
;;; - natural
;;; - symbol
;;; - (list '+ cterm cterm)
;;; - (list '- cterm cterm)
;;; - (list '* constant cterm)
(define/match (cterm? x)
  [((? exact-integer? _)) #t]
  [((? symbol? _)) #t]
  [((list '+ (? cterm? _) (? cterm? _))) #t]
  [((list '- (? cterm? _) (? cterm? _))) #t]
  [((list '* (? exact-integer? _) (? cterm? _))) #t]
  [(_) #f])

;;; Substitute a cterm for a variable inside a cterm
(define (cterm-subst old new ct)
  #;(printf "  replace ~v with ~v in ~v\n"
          old new ct)
  (match ct
    [(? symbol? var) #;(printf "Var case: looking for ~v, found ~v\n"
                             old ct)
                     (if (equal? ct old)
                         (begin #;(printf " ~v = ~v, so replace\n"
                                        ct old) new)
                         ct)]
    [(? exact-integer? n) n]
    [(list (? symbol? op) (? cterm? left) (? cterm? right))
     (list op (cterm-subst old new left) (cterm-subst old new right))]))
(module+ test
  (check-equal? (cterm-subst 'x '(+ 2 (* 9 y))
                             '(+ 6 (+ (* 8 y) (* 3 z))))
                '(+ 6 (+ (* 8 y) (* 3 z))))
  (check-equal? (cterm-subst 'x '(+ 3 (* 2 y))
                             '(+ 3 (+ (* 2 x) (* 4 y))))
                '(+ 3 (+ (* 2 (+ 3 (* 2 y))) (* 4 y)))))


;;;;----------------------------------------------------------------------------
;;;;
;;;;  Flattened representation of constraint terms
;;;;
;;;;----------------------------------------------------------------------------

;;; A flattened constraint terms is
;;;   a hash mapping variable names to their integer coefficients,
;;;   plus a constant integer
(define-struct/contract flattened-cterm
  ([constant exact-integer?]
   [coefficients (hash/c symbol? (and/c exact-integer? (not/c zero?)) #:immutable #t)])
  #:transparent)
(define (fct-uses-var var fct)
  (hash-has-key? (flattened-cterm-coefficients fct) var))
(define (get-coeff var fct)
  (hash-ref (flattened-cterm-coefficients fct) var 0))

;;; Utility function for updating the coefficients array by adding a single (var . coeff)
(define (update-coeff-hash coeffs var delta)
  (define new-coeff (+ delta (hash-ref coeffs var 0)))
  (if (= 0 new-coeff)
      (hash-remove coeffs var)
      (hash-set coeffs var new-coeff)))

;;; Add a single (var . coeff) or number to a flattened constraint term
(define/match (add-fct-atom fct atom)
  [((flattened-cterm const coeffs) (? exact-integer? _))
   (flattened-cterm (+ atom const) coeffs)]
  [((flattened-cterm const coeffs) (list (? symbol? var) (? exact-integer? delta)))
   (flattened-cterm const (update-coeff-hash coeffs var delta))])
(module+ test
  (check-equal? (add-fct-atom (flattened-cterm 3 #hash((x . 2) (y . 4))) 3)
                (flattened-cterm 6 #hash((x . 2) (y . 4))))
  (check-equal? (add-fct-atom (flattened-cterm 3 #hash((x . 2) (y . 4))) '(x 3))
                (flattened-cterm 3 #hash((x . 5) (y . 4))))
  (check-equal? (add-fct-atom (flattened-cterm 3 #hash((x . 2) (y . 4))) '(y 3))
                (flattened-cterm 3 #hash((x . 2) (y . 7))))
  (check-equal? (add-fct-atom (flattened-cterm 3 #hash((x . 2) (y . 4))) '(z 3))
                (flattened-cterm 3 #hash((x . 2) (y . 4) (z . 3))))
  (check-equal? (add-fct-atom (flattened-cterm 3 #hash((x . 2) (y . 4))) '(x -2))
                (flattened-cterm 3 #hash((y . 4)))))

;;; Find the sum of two flattened constraint terms
(define/match (add-fct fct1 fct2)
  [((flattened-cterm const1 coeffs1) (flattened-cterm const2 coeffs2))
   (flattened-cterm (+ const1 const2)
                    (for/fold ([accum coeffs1])
                              ([(var delta) coeffs2])
                      (update-coeff-hash accum var delta)))])
(module+ test
  (check-equal? (add-fct (flattened-cterm 6 #hash((x . 2) (y . 4)))
                         (flattened-cterm 5 #hash((q . 3) (y . 9))))
                (flattened-cterm 11 #hash((q . 3) (x . 2) (y . 13))))
  (check-equal? (add-fct (flattened-cterm 6 #hash((x . 2) (y . 4)))
                         (flattened-cterm 5 #hash((q . 3) (y . -4))))
                (flattened-cterm 11 #hash((q . 3) (x . 2)))))

;;; Multiply a flattened constraint term by a scalar
(define/match (scale-fct fct scal)
  [((flattened-cterm const coeffs) (? exact-integer? _))
   (flattened-cterm (* scal const)
                    (if (= scal 0) #hash()
                        (for/hash ([(var coeff) coeffs])
                          (values var (* scal coeff)))))])
(module+ test
  (check-equal? (scale-fct (flattened-cterm 3 #hash((x . 2) (y . 4))) 3)
                (flattened-cterm 9 #hash((x . 6) (y . 12)))))
;;; Negating a term is just multiplication by -1
(define (negate-fct t) (scale-fct t -1))
(module+ test
  (check-equal? (negate-fct (flattened-cterm 3 #hash((x . 2) (y . 4))))
                (flattened-cterm -3 #hash((x . -2) (y . -4)))))
;;; Subtraction is negation and addition
(define (sub-fct left right) (add-fct left (negate-fct right)))
(module+ test
  (check-equal? (sub-fct (flattened-cterm 1 #hash((x . 2) (y . 4)))
                         (flattened-cterm 6 #hash((z . 3) (y . 4))))
                (flattened-cterm -5 #hash((x . 2) (z . -3)))))

;;; Substitute a flattened-cterm for a variable inside a flattened-cterm
(define (flattened-cterm-subst old new fct)
  (define old-coeff (get-coeff old fct))
  (add-fct
   fct (scale-fct
        (sub-fct new (flattened-cterm 0 (make-immutable-hash `([,old . 1]))))
        old-coeff)))
(module+ test
  (check-equal? (flattened-cterm-subst 'x (flattened-cterm 2 #hash((y . 9)))
                                       (flattened-cterm 6 #hash((y . 8) (z . 3))))
                (flattened-cterm 6 #hash((y . 8) (z . 3))))
  (check-equal? (flattened-cterm-subst 'x (flattened-cterm 3 #hash((y . 2)))
                                       (flattened-cterm 3 #hash((x . 2) (y . 4))))
                (flattened-cterm 9 #hash((y . 8)))))


;;; Convert from syntactic form of a term to the flattened representation
(define/match (syntactic-cterm->flat-cterm _)
  [((? exact-integer? const)) (flattened-cterm const #hash())]
  [((? symbol? var))
   (flattened-cterm 0 (make-immutable-hash (list (cons var 1))))]
  [((list '+ (? cterm? left) (? cterm? right)))
   (add-fct (syntactic-cterm->flat-cterm left)
            (syntactic-cterm->flat-cterm right))]
  [((list '- (? cterm? left) (? cterm? right)))
   (sub-fct (syntactic-cterm->flat-cterm left)
            (syntactic-cterm->flat-cterm right))]
  [((list '* (? exact-integer? scal) (? cterm? ct)))
   (scale-fct (syntactic-cterm->flat-cterm ct) scal)])
(module+ test
  (check-equal? (syntactic-cterm->flat-cterm '(+ (+ 2 x) (+ x 4)))
                (flattened-cterm 6 #hash((x . 2))))
  (check-equal? (syntactic-cterm->flat-cterm '(- (* 3 x) (+ y 4)))
                (flattened-cterm -4 #hash((x . 3) (y . -1)))))
(provide (contract-out [syntactic-cterm->flat-cterm
                        (-> cterm? flattened-cterm?)]))

;;; Utility functions for flat->syntactic conversion
(define/match (cterm-piece _0 _1)
  [((? symbol? var) 1) var]
  [((? symbol? var) (? exact-integer? coeff)) `(* ,coeff ,var)])
(define (assemble-cterm init vars coeffs)
  ;; Sort the var/coeff pairs by descending coefficient
  (define sorted-pairs
    (sort
     (for/list ([var vars] [coeff coeffs]) (cons var coeff))
     (λ (left right) (> (cdr left) (cdr right)))))
  (define sorted-vars (map car sorted-pairs))
  (define sorted-coeffs (map cdr sorted-pairs))
  ;; For a negative constant, subtract it at the end, not the beginning. If
  ;; there are no variable subterms, just use the constant itself.
  (cond [(and (integer? init) (negative? init) (empty? sorted-pairs))
         `(- 0 ,(- init))]
        [(empty? sorted-pairs)
         init]
        [(equal? init 0)
         (for/fold ([subterm (cterm-piece (first sorted-vars)
                                          (first sorted-coeffs))])
                   ([var   (rest sorted-vars)]
                    [coeff (rest sorted-coeffs)])
           (if (negative? coeff)
               `(- ,subterm ,(cterm-piece var (- coeff)))
               `(+ ,subterm ,(cterm-piece var coeff))))]
        [(and (integer? init) (negative? init))
         `(- ,(for/fold ([subterm (cterm-piece (first sorted-vars)
                                          (first sorted-coeffs))])
                        ([var   (rest sorted-vars)]
                         [coeff (rest sorted-coeffs)])
               (if (negative? coeff)
                   `(- ,subterm ,(cterm-piece var (- coeff)))
                   `(+ ,subterm ,(cterm-piece var coeff))))
             ,(- init))]
        [else
         (for/fold ([subterm init])
                   ([var   sorted-vars]
                    [coeff sorted-coeffs])
           (if (negative? coeff)
               `(- ,subterm ,(cterm-piece var (- coeff)))
               `(+ ,subterm ,(cterm-piece var coeff))))]))
;;; Convert flattened term to syntactic version
(define/match (flat-cterm->syntactic-cterm _)
  [((flattened-cterm const (hash-table))) const]
  ;; Removing this case for now because coeff0 might be negative
  #;[((flattened-cterm 0 (hash-table (var0 coeff0) (var1 coeff1) ...)))
   (assemble-cterm (cterm-piece var0 coeff0) var1 coeff1)]
  [((flattened-cterm const (hash-table (var1 coeff1) ...)))
   (assemble-cterm const var1 coeff1)])
(provide (contract-out [flat-cterm->syntactic-cterm (-> flattened-cterm? cterm?)]))
(module+ test
  (check-equal? (flat-cterm->syntactic-cterm (flattened-cterm 0 #hash((x . 3))))
                '(* 3 x))
  (check-equal? (flat-cterm->syntactic-cterm (flattened-cterm 2 #hash((x . 3))))
                '(+ 2 (* 3 x)))
  ;; No guarantees about order when we pull everything out of a hash, so just
  ;; testing for inverse-like behavior.
  (check-equal? (syntactic-cterm->flat-cterm
                 (flat-cterm->syntactic-cterm
                  (flattened-cterm 9 #hash((x . 3) (y . 4) (z . 5)))))
                (flattened-cterm 9 #hash((x . 3) (y . 4) (z . 5)))))

;;; Project out particular variables from a flattened constraint term
(define (fct-project vars fct)
  (define coeffs (flattened-cterm-coefficients fct))
  (flattened-cterm 0
                   (for/hash ([var vars]
                              #:when (hash-has-key? coeffs var))
                     (values var (hash-ref coeffs var)))))
(module+ test
  (check-equal? (fct-project '(w x y) (flattened-cterm 9 #hash((x . 3) (y . 4) (z . 5))))
                (flattened-cterm 0 #hash((x . 3) (y . 4)))))

;;;;----------------------------------------------------------------------------
;;;;
;;;;  Flattened representation of an index instantiation constraint
;;;;
;;;;----------------------------------------------------------------------------

;;; The constraint for instantiating a  takes the form
;;;   (∀ (x ...) (cform -> cfrom ^ (∃ (y ...) cform)))
;;; The cformulas should both be conjunctions of equalities.
;;; It is represented as a structure:
(define flattened-equality? (list/c flattened-cterm? '≐ flattened-cterm?))
(define flattened-inequality? (list/c flattened-cterm? '≤ flattened-cterm?))
(define flattened-atomic? (or/c flattened-equality?
                                flattened-inequality?))
(define-struct/contract instantiation-constraint
  ([univ-vars (listof symbol?)]
   [premise-eqs (listof flattened-atomic?)]
   [conclusion-eqs (listof flattened-atomic?)]
   [ex-vars (listof symbol?)]
   [ex-eqs (listof flattened-atomic?)])
  #:transparent)
(provide (struct-out instantiation-constraint))
;;; Wrapper for the instantiation-constraint constructor so that other modules
;;; don't have to deal with inez-wrapper's flattened term IR.
(define (syntactic≐->flat≐ e)
  (list (syntactic-cterm->flat-cterm (first e)) '≐ (syntactic-cterm->flat-cterm (third e))))
(define (syntactic≤->flat≤ e)
  (list (syntactic-cterm->flat-cterm (first e)) '≤ (syntactic-cterm->flat-cterm (third e))))
(define/match (syntactic-atom->flat-atom e)
  [((list _ '≐ _)) (syntactic≐->flat≐ e)]
  [((list _ '≤ _)) (syntactic≤->flat≤ e)])
(define (build-instantiation-constraint univ-vars
                                        premise-eqs
                                        conclusion-eqs
                                        ex-vars
                                        ex-eqs)
  (instantiation-constraint univ-vars
                            (map syntactic-atom->flat-atom premise-eqs)
                            (map syntactic-atom->flat-atom conclusion-eqs)
                            ex-vars
                            (map syntactic-atom->flat-atom ex-eqs)))
(provide (contract-out [build-instantiation-constraint
                        (-> (listof symbol?) (listof cform?) (listof cform?)
                            (listof symbol?) (listof cform?)
                            instantiation-constraint?)]))

;;; Nicer way to show a flattened equality
(define (flat≐->string e)
  (format "~v ≐ ~v\n" (flat-cterm->syntactic-cterm (first e)) (flat-cterm->syntactic-cterm (third e))))
(define (flat≐->syntactic≐ e)
  (list (flat-cterm->syntactic-cterm (first e)) '≐ (flat-cterm->syntactic-cterm (third e))))
(define (flat≤->syntactic≤ e)
  (list (flat-cterm->syntactic-cterm (first e)) '≤ (flat-cterm->syntactic-cterm (third e))))
(define/match (flat-atom->syntactic-atom e)
  [((? flattened-equality? _)) (flat≐->syntactic≐ e)]
  [((? flattened-inequality? _)) (flat≤->syntactic≤ e)])

;;; Deterine whether an equality mentions some variable
;;; TODO: Don't return #t if the var is used only trivially, like in 0 ≤ x -- if
;;; any arbitrary natural number could work, we know nothing about the variable.
;;; Fully general form would have to know what the universal variables and
;;; premises are, to ask whether ∀univs.(Φ->eqn).
(define (eq-uses-var? e var)
  (and (or (fct-uses-var var (first e)) (fct-uses-var var (third e)))
       ;; simple exception case: 0 ≤ x
       (match e
         [(list (flattened-cterm 0 (hash-table)) '≤ (flattened-cterm 0 (hash-table (v c))))
          (equal? var v)]
         [_ #t])
       #;...))

;;; Isolate chosen variables on one side
(define/match (solve-for* vars _)
  [(_ (list (? flattened-cterm? left) (? (or/c '≐ '≤) pred) (? flattened-cterm? right)))
   ;; Move RHS vars components to left
   (define rhs-vars-component (fct-project vars right))
   (define left2 (sub-fct left rhs-vars-component))
   (define right2 (sub-fct right rhs-vars-component))
   ;; Move LHS non-vars components to right
   (define non-vars
     (set-subtract (list->set (hash-keys (flattened-cterm-coefficients left2)))
                   (for/set ([v vars]) v)))
   (define lhs-non-vars-component (fct-project non-vars left))
   (define left3 (sub-fct left2 lhs-non-vars-component))
   (define right3 (sub-fct right2 lhs-non-vars-component))
   ;; Move constant component from left to right
   (define neg-lhs-const (- (flattened-cterm-constant left3)))
   (list (add-fct-atom left3 neg-lhs-const) pred (add-fct-atom right3 neg-lhs-const))])
(define (solve-for var e)
  (match (solve-for* (list var) e)
    ;; left-coeffs should be singleton hash, with var as only key
    [(list (flattened-cterm 0 left-coeffs) (? (or/c '≐ '≤) pred)
           (flattened-cterm right-const right-coeffs))
     (define left-coeff (hash-ref left-coeffs var 1))
     (list (flattened-cterm 0 (make-immutable-hash (list (cons var 1))))
           pred
           (flattened-cterm
            (quotient right-const left-coeff)
            (for/hash ([(v c) right-coeffs]
                       #:when (begin0
                                (not (zero? (quotient c left-coeff)))
                                #;(printf "SOLVE_FOR: Including ~v * ~v\n"
                                          v (quotient c left-coeff))))
                      (values v (quotient c left-coeff)))))]))
(module+ test
  (check-equal? (solve-for*
                 '(w z)
                 (list (flattened-cterm 9 #hash((w . 8) (x . 3)))
                       '≐
                       (flattened-cterm 6 #hash((y . 4) (z . 2)))))
                (list (flattened-cterm 0 #hash((w . 8) (z . -2)))
                      '≐
                      (flattened-cterm -3 #hash((y . 4) (x . -3)))))
  (check-equal? (solve-for*
                 '(w z)
                 (list (flattened-cterm 9 #hash((w . 8) (x . 3)))
                       '≤
                       (flattened-cterm 6 #hash((y . 4) (z . 2)))))
                (list (flattened-cterm 0 #hash((w . 8) (z . -2)))
                      '≤
                      (flattened-cterm -3 #hash((y . 4) (x . -3)))))
  (check-equal? (solve-for 'z
                           (list (flattened-cterm 90 #hash((w . 8) (x . 30)))
                                 '≐
                                 (flattened-cterm 6 #hash((y . 4) (z . 2)))))
                (list (flattened-cterm 0 #hash((z . 1)))
                      '≐
                      (flattened-cterm 42 #hash((y . -2) (w . 4) (x . 15))))))


;;;;----------------------------------------------------------------------------
;;;;
;;;;  Quantifier elimination preprocessing
;;;;
;;;;----------------------------------------------------------------------------

;;; Rewrite the ∃-quantified equations so each variable appears only on one side
(define/match (single-var-appearance e)
  [((list (? flattened-cterm? left) (? (or/c '≐ '≤) pred) (? flattened-cterm? right)))
   (define left-keys (list->set (hash-keys (flattened-cterm-coefficients left))))
   (define right-keys (list->set (hash-keys (flattened-cterm-coefficients right))))
   (define overlap-vars (set-intersect left-keys right-keys))
   (cond
     ;; Disjoint key sets -> return the same equation unchanged
     [(set-empty? overlap-vars) e]
     ;; Otherwise, subtract the overlap from both sides
     [else (define overlap-fct (fct-project overlap-vars left))
           (list (sub-fct left overlap-fct) pred
                 (sub-fct right overlap-fct))])])
(module+ test
  (check-equal? (single-var-appearance
                 (list (flattened-cterm 9 #hash((w . 8) (x . 3) (z . 3)))
                       '≐
                       (flattened-cterm 6 #hash((x . 1) (y . 4) (z . 5)))))
                (list (flattened-cterm 9 #hash((w . 8)))
                      '≐
                      (flattened-cterm 6 #hash((x . -2) (y . 4) (z . 2)))))
  (check-equal? (single-var-appearance
                 (list (flattened-cterm 9 #hash((w . 8) (x . 3) (z . 3)))
                       '≤
                       (flattened-cterm 6 #hash((x . 1) (y . 4) (z . 5)))))
                (list (flattened-cterm 9 #hash((w . 8)))
                      '≤
                      (flattened-cterm 6 #hash((x . -2) (y . 4) (z . 2))))))

;;; Simplify quantifier elimination by pulling the equalities that don't
;;; mention any existential variables outside of the ∃ quantifier.
(define (fct-mentions-exvars? vars fct)
  (for/or ([var vars])
    (hash-has-key? (flattened-cterm-coefficients fct) var)))
(define (eq-mentions-exvars? vars equality)
  (or (fct-mentions-exvars? vars (first equality))
      (fct-mentions-exvars? vars (third equality))))
(define/match (lift-∃-invariants ict)
  [((instantiation-constraint ∀v pe ce ∃v ∃e))
   (define-values (stay move)
     (partition ((curry eq-mentions-exvars?) ∃v) ∃e))
   (instantiation-constraint ∀v pe (append ce move) ∃v stay)])

;;; Full preprocessing procedure
(define/match (preprocess-instantiation-constraint ict)
  [((instantiation-constraint ∀v pe ce ∃v ∃e))
   (lift-∃-invariants
    (instantiation-constraint ∀v (map single-var-appearance pe)
                              (map single-var-appearance ce)
                              ∃v (map single-var-appearance ∃e)))])


;;;;----------------------------------------------------------------------------
;;;;
;;;;  Removing a quantified variable
;;;;
;;;;----------------------------------------------------------------------------

;;; Next, the ∃-quantified equations must be rewritten so that the first
;;; existential variable appears with the same coeficient every time.
(define (coeffs-of var eqs)
  (set-union (for/set ([e eqs]
                       #:when (fct-uses-var var (first e)))
               (get-coeff var (first e)))
             (for/set ([e eqs]
                       #:when (fct-uses-var var (third e)))
               (get-coeff var (third e)))))
(module+ test
  (check-equal? (coeffs-of 'x (list (list (flattened-cterm 9 #hash((w . 8) (x . 3)))
                                          '≐
                                          (flattened-cterm 6 #hash((y . 4) (z . 2))))
                                    (list (flattened-cterm 9 #hash((w . 8) (z . 3)))
                                          '≐
                                          (flattened-cterm 6 #hash((y . 4))))
                                    (list (flattened-cterm 9 #hash((w . 8) (z . 3)))
                                          '≐
                                          (flattened-cterm 6 #hash((y . 4) (x . 5))))))
                (set 3 5)))
(define/match (scale-coeff var new-coeff _)
  [(_ _ (list (? flattened-cterm? left) (? (or/c '≐ '≤) pred) (? flattened-cterm? right)))
   (define scale-factor
     (cond [(fct-uses-var var left) (quotient new-coeff (get-coeff var left))]
           [(fct-uses-var var right) (quotient new-coeff (get-coeff var right))]
           [else 1]))
   (list (scale-fct left scale-factor) pred (scale-fct right scale-factor))])
(module+ test
  (check-equal? (scale-coeff 'w 16
                             (list (flattened-cterm 9 #hash((w . 8) (z . 3)))
                                   '≐
                                   (flattened-cterm 6 #hash((y . 4)))))
                (list (flattened-cterm 18 #hash((w . 16) (z . 6)))
                                   '≐
                                   (flattened-cterm 12 #hash((y . 8)))))
  (check-equal? (scale-coeff 'w 16
                             (list (flattened-cterm 9 #hash((w . 8) (z . 3)))
                                   '≤
                                   (flattened-cterm 6 #hash((y . 4)))))
                (list (flattened-cterm 18 #hash((w . 16) (z . 6)))
                                   '≤
                                   (flattened-cterm 12 #hash((y . 8))))))
(define/match (scale-∃var-coeffs ict)
  [((instantiation-constraint ∀v pe ce ∃v ∃e))
   ;; Identify the ∃var we're eliminating, get the lcm of all its coefficients,
   ;; then scale the equalities that use it to match that lcm.
   (define elim-var (first ∃v))
   (define new-coeff (apply lcm (set->list (coeffs-of elim-var ∃e))))
   (list elim-var
         new-coeff
         (instantiation-constraint
          ∀v pe ce ∃v
          (for/list ([e ∃e])
            (scale-coeff elim-var new-coeff e))))])
(module+ test
  (check-equal? (scale-∃var-coeffs
                 (instantiation-constraint
                  '(w) '() '() '(z y x)
                  (list (list (flattened-cterm 9 #hash((w . 8) (x . 3)))
                              '≐
                              (flattened-cterm 8 #hash((y . 4) (z . 2))))
                        (list (flattened-cterm 7 #hash((w . 8) (z . 3)))
                              '≐
                              (flattened-cterm 6 #hash((y . 4))))
                        (list (flattened-cterm 5 #hash((w . 7)))
                              '≐
                              (flattened-cterm 4 #hash((y . 4) (x . 5)))))))
                (list
                 'z
                 6
                 (instantiation-constraint
                  '(w) '() '() '(z y x)
                  (list (list (flattened-cterm 27 #hash((w . 24) (x . 9)))
                              '≐
                              (flattened-cterm 24 #hash((y . 12) (z . 6))))
                        (list (flattened-cterm 14 #hash((w . 16) (z . 6)))
                              '≐
                              (flattened-cterm 12 #hash((y . 8))))
                        (list (flattened-cterm 5 #hash((w . 7)))
                              '≐
                              (flattened-cterm 4 #hash((y . 4) (x . 5)))))))))

;;; Once the first existential variable n appears with the same coefficient p
;;; every time, we can choose a fresh name m to represent p*n.
(define/match (fct-replace-var fct old-var new-var)
  [((flattened-cterm const coeffs) _ _)
   (if (hash-has-key? coeffs old-var)
       (flattened-cterm const (hash-set (hash-remove coeffs old-var) new-var 1))
       fct)])

;;; With the new variable m isolated on the left side of an equality, the right
;;; side gives instructions for rewriting it in terms of other variables.
;;; Replace all occurrences of m with that expansion.
(define/match (expand-var old-var expansion original)
  [(_ _ (flattened-cterm const coeffs))
   (define old-var-coeff (hash-ref coeffs old-var 0))
   (define expansion-component (scale-fct expansion old-var-coeff))
   (add-fct expansion-component
            (flattened-cterm const (hash-remove coeffs old-var)))])
(module+ test
  (check-equal? (expand-var 'q (flattened-cterm 1 #hash((x . 2)))
                            (flattened-cterm 6 #hash((y . 4) (z . 2))))
                (flattened-cterm 6 #hash((y . 4) (z . 2))))
  (check-equal? (expand-var 'y (flattened-cterm 1 #hash((x . 2)))
                            (flattened-cterm 6 #hash((y . 4) (z . 2))))
                (flattened-cterm 10 #hash((x . 8) (z . 2)))))


;;; The complete loop:
;;; 1. preprocess constraint
;;; 2. unify the coefficients of the first ∃var
;;; 3. choose a fresh var to represent the first ∃var and its coefficient
;;; 4. isolate the fresh var in some equality where it appears
;;; 5. replace uses of the fresh var with its expansion determined in step 4
;;; TODO: 6. add an inequality constraining that expansion to be nonnegative
;;; Returns list containing
;;; - equality for substituting the eliminated exvar
;;; - list of equalities for substituting temporary exvars
;;; - what term must now be a multiple of what number
;;; - new constraint
(define (remove-one-∃var ict)
  (match (scale-∃var-coeffs (preprocess-instantiation-constraint ict))
    [(list elim-var elim-coeff (instantiation-constraint ∀v pe ce ∃v ∃e))
     (define fresh-∃var
       (gensym (string-append "exvar_" (symbol->string elim-var) "_")))
     (define new-∃e
       (append
       (for/list ([e ∃e])
          (define new-left (fct-replace-var (first e) elim-var fresh-∃var))
          (define new-right (fct-replace-var (third e) elim-var fresh-∃var))
          #;(printf "Turning ~v into ~v\n" e (list new-left '≐ new-right))
          (list new-left (second e) new-right))))
     ;; If there are no still-used exvars, for/first will return #f.
     (define next-∃var
       (for/first ([e new-∃e]
                   #:when (and (flattened-equality? e)
                               (eq-uses-var? e fresh-∃var)
                               #;(begin (printf "exvar ~v is used in ~v\n" fresh-∃var e) #t)))
                  e))
     (if next-∃var
         (let-values ([(expanded-∃e new-∃var-expansion)
                       (let* ([new-∃var-solution (solve-for fresh-∃var next-∃var)]
                              [new-∃var-expansion (third new-∃var-solution)])
                         (values
                          (cons
                           ;; New inequality constraining the ∃var's expansion
                           `(,(syntactic-cterm->flat-cterm 0) ≤ ,new-∃var-expansion)
                           (for/list
                            ([e new-∃e])
                            (single-var-appearance
                             (list (expand-var fresh-∃var new-∃var-expansion (first e)) '≐
                                   (expand-var fresh-∃var new-∃var-expansion (third e))))))
                          new-∃var-expansion))])
           (list
            ;; Equality for the eliminated existential variable, so we can later write
            ;; it in terms of universal variables
            (flat-atom->syntactic-atom
             (solve-for* (list elim-var)
                         `(,(syntactic-cterm->flat-cterm `(* ,elim-coeff ,elim-var))
                           ≐ ,new-∃var-expansion)))
            ;; Substitution for the generated temporary exvar, if one was generated
            (if next-∃var
                (list `(,fresh-∃var ≐ ,(flat-cterm->syntactic-cterm
                                        new-∃var-expansion)))
                '())
            ;; We need to ensure that our newly generated existential variable
            ;; really is a multiple of the coefficient of the variable we eliminate.
            `(,(flat-cterm->syntactic-cterm new-∃var-expansion) divisible ,elim-coeff)
            ;; Updated version of instantiation constraint
            (instantiation-constraint ∀v pe ce (remove elim-var ∃v) expanded-∃e)))
         (begin
           #;(printf "dropping an exvar\n")
           (list
            ;; The substitution equality for unused var x is x=x
            (list 0 '≐ 0)
            ;; No substitutions needed
            '()
            ;; Divisibility constraint placeholder
            '(1 divisible 1)
            ;; Drop the unused var, leaving the rest of the constraint untouched
            (instantiation-constraint ∀v pe ce (remove elim-var ∃v) ∃e))))]))

;;; TODO: Wrap this in an idx-arg-query function which returns either a term
;;; (which should be used as the index argument) or something to indicate error.
;;; TODO: The accumulated list of substitutions may include multiple assignments
;;; for the same variable. Dumping them all into a hash should deduplicate, but
;;; does it matter *which* substitutions get dropped? Actually, it's probably
;;; better to inline all the temporaries' assignments and to only have program
;;; exvars used in the substitution list.
(define (remove-all-∃vars ict)
  (define (helper freshvar-eqs divisibilities ict)
    (if (empty? (instantiation-constraint-ex-vars ict))
        (list freshvar-eqs divisibilities ict)
        (let ([next-ixt (remove-one-∃var ict)])
          (helper (cons (first next-ixt)
                        (append (second next-ixt) freshvar-eqs))
                  ;; Drop "divisibility by one" rules
                  (if (equal? 1 (third (third next-ixt)))
                      divisibilities
                      (cons (third next-ixt) divisibilities))
                  (fourth next-ixt)))))
  (helper '() '() ict))
;;; Determine whether an index instantiation constraint is valid. If it is
;;; valid, return a list containing #t and a list of symbolic descriptions of
;;; each existential variable (in terms of the universal variables). Otherwise,
;;; return a list containing #f and an assignment for the universal variables
;;; that makes the existential variables unsolvable.
(define (instantiate ict)
  (define initial-∃vars (instantiation-constraint-ex-vars ict))
  (define ∀vars (instantiation-constraint-univ-vars ict))
  (match-define (list substs divisibilities final-form)
    (remove-all-∃vars ict))
  (define candidate-witnesses
    (for/list ([eqn (inline-var-defns ∀vars substs)]
               #:when (member (first eqn) initial-∃vars))
              ;; Flatten and unflatten to simplify the witness expression
              (flat≐->syntactic≐ (syntactic≐->flat≐ eqn))))
  ;(printf "Candidate witnesses: ~v\n\n" candidate-witnesses)
  (define premises
    (append '[] (map flat-atom->syntactic-atom
                     (instantiation-constraint-premise-eqs final-form))))
  ;(printf "Premises: ~v\n\n" premises)
  (define conclusions
    ;; These need to get folded into a single formula
    (foldr (λ (l r) `(AND ,l ,r)) '(0 ≐ 0)
           (map flat-atom->syntactic-atom
                (append (instantiation-constraint-conclusion-eqs final-form)
                        (instantiation-constraint-ex-eqs final-form)))))
  ;(printf "Conclusions: ~v\n\n" conclusions)
  ;; At this point, we have a closed, universally-quantified implication:
  ;;   ∀ x... . (Φ ⇒ Ψ)   =   ∀ x... . (¬Φ ∨ Ψ)
  ;; where Φ contains facts we've been carrying along in the type checking
  ;; environment, and Ψ contains facts that constrain our choice of indices to
  ;; use as instantiation arguments.
  ;;
  ;; We actually have some extra information about some variables, saying that
  ;; they must be multiples of some particular constants. We'll call the
  ;; conjunction of "multiple-of" requirements Ξ:
  ;;    ∀ x... . (¬Φ ∨ (Ψ ∧ Ξ))
  ;;
  ;; By quantifier rotation, this is equivalent to the formula:
  ;;   ¬ ∃ x... . ¬(¬Φ ∨ (Ψ ∧ Ξ))   =   ¬ ∃ x... . (Φ ∧ (¬Ψ ∨ ¬Ξ))
  ;; We want to know whether the formula holds. This is equivalent to asking
  ;; whether the existentially quantified piece is unsatisfiable:
  ;;   UNSAT(Φ ∧ (¬Ψ ∨ ¬Ξ))
  ;;
  ;; Ψ and Ξ are both conjunctions of atomic formulae, so their negations are
  ;; disjunctions of atomic formulae. Inez's Presburger logic is able to express
  ;; the components of Ψ directly but not those of Ξ. We have to introduce a
  ;; universally quantified variable to say "x is a multiple of k," but that
  ;; means saying "x is not a multiple of k" requires a new existentially
  ;; quantified variable. That we can do in a satisfiability query by simply
  ;; inserting new free variables "q" and "r" for the quotient and remainder:
  ;;    x = k*q + r ∧ 1 ≤ r ∧ r < k
  ;;
  ;; So the components we have are "premises," "conclusions," and "multiples."
  ;; Premises appear as we obtian them from the instantiation constraint and can
  ;; be handed directly to racket->inez to generate Inez code.
  ;; Conclusions get wrapped in a negation before being handed to racket->inez.
  ;; Multiples need to be stepped through one at a time, with the resulting
  ;; conjunctions then assembled into one disjunction-of-conjunctions, which can
  ;; be processed by racket->inez.
  ;;
  (define extended-conclusions
    (begin
      (foldr (λ (divisibility accum)
               (let ([mult-var (first divisibility)]
                     [divisor-const (third divisibility)]
                     [quotient (gensym "quot_")]
                     [remainder (gensym "rem_")])
                 `(NOT
                   (AND (NOT ,accum)
                        (NOT (AND (,mult-var ≐ (+ (* ,divisor-const ,quotient)
                                                  ,remainder))
                                  (AND (1 ≤ ,remainder)
                                       ((+ 1 ,remainder)
                                        ≤ ,divisor-const))))))))
             `(NOT ,conclusions)
             divisibilities)))
  ;(printf "Extended conclusions: ~v\n\n" extended-conclusions)
  (define unsat-check-formula
    (foldr (λ (premise conclusion) `(AND ,premise ,conclusion))
           extended-conclusions
           premises))
  ;(printf "UNSAT instance: ~v\n\n" unsat-check-formula)
  (define print-sat-asmt
    (apply string-append
           ;; Instead of asking about all of the universal vars, only ask about
           ;; the ones mentioned in the formula (because the preamble won't even
           ;; introduce those that don't get mentioned).
           (for/list ([v (constraint-vars unsat-check-formula) #;∀vars])
                     ;; ideref_printf "⟨v⟩ = %i:\n" ⟨v⟩ ;;
                     (string-append "ideref_printf \""
                                    (symbol->string v)
                                    " = %i\\n\" "
                                    (symbol->string v)
                                    " ;;\n"))))
  ;; This Inez script determines whether there is a satisfying assignment for
  ;; the ∀vars (from the original instantiation constraint). If so, that's a
  ;; choice of ∀vars for which no choice of ∃var witness can satisfy the
  ;; requirements for index instantiation. In that case, Inez will say "sat" or
  ;; "opt" as the first line of its response, and the following lines will
  ;; identify the value chosen for each ∀var. Otherwise, Inez should say "unsat"
  ;; indicating that every possible choice of ∀vars admits an assignment of
  ;; witnesses to ∃vars, and the substitutions discovered in eliminating the
  ;; existential quantifier can describe those witnesses in terms of the ∀vars.
  (define unsat-script
    (string-append
     (preamble '() unsat-check-formula) "\n"
     "constrain (~logic " (racket->inez unsat-check-formula) ") ;;\n\n"
     "solve_print_result();;\n"
     print-sat-asmt))
  ;(printf "UNSAT script:\n~a\n\n" unsat-script)
  (define script-file (make-temporary-file "Inez_~a.ml"))
  ;(printf "Created file ~v\n" script-file)
  (define script-port (open-output-file script-file
                                        #:exists 'truncate))
  (display unsat-script script-port)
  (close-output-port script-port)
  ;(printf "Wrote script into ~v\n" script-file)
  (define-values (inez-process inez-stdout inez-stdin inez-stderr)
    (subprocess #f #f #f
                (find-executable-path "inez.opt")
                script-file))
  ;(printf "\nInez process spun off\n\n")
  (define inez-output (port->string inez-stdout))
  ;(printf "Inez is done\n\n")
  (close-input-port inez-stdout)
  (close-output-port inez-stdin)
  (close-input-port inez-stderr)
  (delete-file script-file)
  (define inez-lines (string-split inez-output "\n"))
  ;(printf "Inez returns:\n~v\n" inez-output)
  (define inez-result (first inez-lines))
  (if (equal? inez-result "unsat")
      (debug-ret "~v\n"
                 (list #t candidate-witnesses))
      (debug-ret "~v\n"
                 (list #f (for/list ([eqn (rest inez-lines)])
                                    (let* ([str-port (open-input-string eqn)]
                                           [var (read str-port)]
                                           [_ (read str-port)]
                                           [value (read str-port)])
                                      (list var '≐ value)))))))
(provide (contract-out [instantiate
                        (-> instantiation-constraint?
                            (list/c boolean?
                                    (listof (list/c symbol? '≐ cterm?))))]))
(define (instantiable? ict) (first (instantiate ict)))
(provide (contract-out [instantiable?
                        (-> instantiation-constraint?
                            boolean?)]))
(module+ test
  (define (check-instantiable . args)
    (check-not-false (first (instantiate (apply build-instantiation-constraint args)))))
  (define (check-not-instantiable . args)
    (check-false (first (instantiate (apply build-instantiation-constraint args)))))
  (check-not-instantiable (term [x])
                          '()
                          '()
                          (term [n])
                          (term [((+ 1 n) ≐ x)]))
  (check-instantiable (term [x])
                      '()
                      '()
                      (term [n])
                      (term [(n ≐ (+ 1 x))]))
  (check-not-instantiable (term [x])
                          '()
                          '()
                          (term [n])
                          (term [((+ n n) ≐ x)]))
  (check-not-instantiable (term [x])
                          '()
                          '()
                          (term [n])
                          (term [((+ n n) ≐ (+ 1 x))]))
  (check-not-instantiable (term [x y])
                          '((x ≐ (+ y y)))
                          '()
                          (term [n])
                          (term [((+ 2 n) ≐ x)]))
  (check-instantiable (term [x y])
                      '((x ≐ (+ y y)))
                      '()
                      (term [n])
                      (term [((+ n n) ≐ x)]))
  (check-instantiable (term [x y z])
                      '((x ≐ (+ y y))
                        (x ≐ (+ 1 z)))
                      '()
                      (term [n])
                      (term [((+ n n) ≐ x)]))
  (check-not-instantiable (term [x y z])
                          '((x ≐ (+ y y))
                            (x ≐ (+ 1 z)))
                          '()
                          (term [n])
                          (term [((+ 1 (+ n n)) ≐ x)]))
  (check-instantiable (term [])
                      '()
                      '()
                      (term [m l])
                      (term ([0 ≐ l])))
  (check-instantiable (term [])
                      '()
                      '()
                      (term [l m])
                      (term ([0 ≐ l])))
  ;; Ensure that the solution appears in the right form
  (check-equal? (instantiate
                    (build-instantiation-constraint
                     '(l a b)
                     '((a ≐ (+ 1 b)) ((+ l l) ≐ (+ 1 a)))
                     '()
                     '(w x y z)
                     '(((+ 1 y) ≐ l))))
                '(#t ((y ≐ (- l 1))))))

;;; Replace all temporary exvars with their definitions so that resulting
;;; definitions are only in terms of "acceptable" variables. Pass a set of
;;; acceptable basis variables that are not defined in terms of anything else
;;; and a list of variable definitions as cforms.
(define (inline-var-defns basis-vars orig-defns)
  ;; Termination condition: Do any definitions use a non-base variable?
  (define used-vars (foldr set-union (set)
                           (map (compose list->set
                                         hash-keys
                                         flattened-cterm-coefficients
                                         syntactic-cterm->flat-cterm
                                         third)
                                orig-defns)))
  (define/match (inline-single defn)
    [((list lhs '≐ rhs))
     (list lhs '≐
           (foldr (λ (sub old-rhs)
                    (cterm-subst (first sub) (third sub) old-rhs))
                  rhs
                  orig-defns))])
  (if (subset? used-vars (list->set basis-vars))
      orig-defns
      ;; Alternative termination condition: we reach fixed point
      ;; TODO: Should this one just subsume the other?
      (let ([new-defns (map inline-single orig-defns)])
        (if (equal? orig-defns new-defns)
            orig-defns
            (inline-var-defns basis-vars new-defns)))))


;;;;----------------------------------------------------------------------------
;;;;
;;;;  Constructing Inez script for validity checking
;;;;
;;;;----------------------------------------------------------------------------

;;; Inez script (string) form of a formula to include in the constraint query
(define/match (racket->inez f)
  [((list op1 '≐ op2))
   (string-append "(" (racket->inez op1) " = " (racket->inez op2) ")")]
  [((list op1 '≤ op2))
   (string-append "(" (racket->inez op1) " <= " (racket->inez op2) ")")]
  [((list 'AND op1 op2))
   (string-append "(" (racket->inez op1) " && " (racket->inez op2) ")")]
  [((list 'NOT op))
   (string-append "(not " (racket->inez op) ")")]
  [((list '+ op1 op2))
   (string-append "(" (racket->inez op1) " + " (racket->inez op2) ")")]
  [((list '- op1 op2))
   (string-append "(" (racket->inez op1) " - " (racket->inez op2) ")")]
  [((list '* (? exact-integer? int) (? symbol? sym)))
   (string-append "(" (racket->inez int) " * " (racket->inez sym) ")")]
  [((? exact-integer? int)) (number->string int)]
  [((? symbol? sym)) (symbol->string sym)]
  [(_) (error "Can't convert from racket data to inez syntax:" f)])

;;; Identify all variables used in a formula/term
(define/match (constraint-vars f)
  [((list op1 '≐ op2)) (remove-duplicates
                        (append (constraint-vars op1) (constraint-vars op2)))]
  [((list op1 '≤ op2)) (remove-duplicates
                        (append (constraint-vars op1) (constraint-vars op2)))]
  [((list 'AND op1 op2)) (remove-duplicates
                          (append (constraint-vars op1) (constraint-vars op2)))]
  [((list 'NOT op)) (constraint-vars op)]
  [((list '+ op1 op2)) (remove-duplicates
                        (append (constraint-vars op1) (constraint-vars op2)))]
  [((list '- op1 op2)) (remove-duplicates
                        (append (constraint-vars op1) (constraint-vars op2)))]
  [((list '*
          (? exact-integer? int)
          (? symbol? sym)))
   (remove-duplicates (constraint-vars sym))]
  [((? exact-integer? int)) '()]
  [((? symbol? sym)) `(,sym)])
(module+ test
  (check-equal? (list->set (constraint-vars
                            (term (AND ((+ x 3) ≐ q) ((+ y x) ≐ (+ z q))))))
                (set 'q 'x 'y 'z)))

;;; Generate calls to fresh_int_var and ≥0 constraints for all vars in a list
(define (var-setup-lines vars)
    (for/fold ([code ""])
      ([var vars])
      (string-append code
                     "let " (symbol->string var) " = fresh_int_var() ;;\n"
                     "constrain (~logic ("
                     (symbol->string var)
                     " >= 0)) ;;\n")))


;;; Inez script "preamble" which opens necessary modules and prepares free
;;; variables used in the givens and constraint
(define (preamble givens formula)
  (define vars (remove-duplicates
                (apply append
                       (constraint-vars formula)
                       (for/list ([g givens]) (constraint-vars g)))))
  (string-append "open Script ;;\n\n" (var-setup-lines vars) "\n"))

;;; Inez script code to set up givens as constraints
(define (constrain-givens givens)
  (for/fold ([code ""])
    ([g givens])
    (string-append
     code
     "constrain (~logic " (racket->inez g) ") ;;\n")))

;;; Inez script to check whether a formula is valid under some givens
;;; Iff Inez returns "unsat," the formula is valid
(define (validity-script givens formula)
  (string-append
   (preamble givens formula)
   (constrain-givens givens)
   "\n"
   "constrain (~logic " (racket->inez (list 'NOT formula)) ") ;;\n\n"
   "solve_print_result() ;;\n"))


;;;;----------------------------------------------------------------------------
;;;;
;;;;  Invoking Inez
;;;;
;;;;----------------------------------------------------------------------------

;;; Invoke Inez to determine whether a formula is valid under some givens
;;; givens is a DKDML-explicit:idx-eqs -- a term of the form ((≐ idx idx) ...)
;;; formula is a term of the form (idx ≐ idx)
(define (inez-valid? givens formula)
  ;; create Inez script file
  (define script-file (make-temporary-file "Inez_~a.ml"))
  #;(printf "created temp file ~v\n" script-file)
  (define script-port (open-output-file script-file
                                        #:exists 'truncate))
  (display (validity-script givens formula) script-port)
  #;(printf "Inez validity script:\n~a\n\n" (validity-script givens formula))
  (close-output-port script-port)
  ;; invoke Inez and watch for result
  (define-values (inez-process inez-stdout inez-stdin inez-stderr)
    (subprocess #f #f #f
                (find-executable-path "inez.opt")
                script-file))
  (define inez-result (port->string inez-stdout))
  #;(printf "Inez result:\n~a\n\n" inez-result)
  ;; cleanup
  (close-input-port inez-stdout)
  (close-output-port inez-stdin)
  (close-input-port inez-stderr)
  (delete-file script-file)
  ;; Formula is valid iff its negation is unsatisfiable
  (equal? inez-result "unsat\n"))

;;; Destruct a constraint term-or-formula by pattern matching
#; (define/match (function-name f)
     [((list op1 '≐ op2)) ]
     [((list 'AND op1 op2)) ]
     [((list 'NOT op)) ]
     [((list '+ op1 op2)) ]
     [((list '- op1 op2)) ]
     [((? exact-nonnegative-integer? int)) ]
     [((? symbol? sym)) ])

;; TODO: figure out how to get DrRacket to see a user's changes to $PATH
(module+ test
  (check-true
   (inez-valid?
    (term ([x ≐ (+ y z)] [(+ 4 z) ≐ (+ y x)]))
    (term ((+ 4 z) ≐ (+ (+ y z) y)))))
  (check-false
   (inez-valid?
    (term ([x ≐ (+ y z)] [(+ 4 z) ≐ (+ y x)]))
    (term ((+ 4 z) ≐ (+ (+ y z) x)))))
  (check-true
   (inez-valid?
    (term ([(+ 8 x) ≐ (+ y z)] [(+ 2 z) ≐ (+ y x)] [(+ 1 y) ≐ z]))
    (term ((+ 2 x) ≐ y)))))

;; Inez seems to have some trouble solving this one
#;
(inez-valid?
    (term ([x ≐ (+ y z)] [(+ 3 z) ≐ (+ y x)]))
    (term ((+ 3 z) ≐ (+ (+ 0 z) y))))
