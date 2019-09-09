#lang racket

(require redex
         makanin/solve
         "language.rkt"
         "implicit-lang.rkt"
         "elab-lang.rkt"
         (for-syntax syntax/parse
                     racket/syntax))
(provide solutions)
(module+ test
  (require rackunit))

;;; Define predicates which recognize syntax classes from a Redex language
(define-syntax (redex-syntax-class stx)
  (syntax-parse stx
    [(_ lang:id class-name:id)
     (let ([pred-name (format-id #'class-name "~a?" (syntax-e #'class-name))])
     #`(define (#,pred-name x) (redex-match lang class-name x)))]
    [(_ lang:id class-name:id ...)
     #`(begin (redex-syntax-class lang class-name) ...)]))
(redex-syntax-class
 Remora-elab
 tvar atmvar arrvar ivar dvar svar evar var
 exatmvar exarrvar exdvar exsvar
 type atmtype arrtype idx dim shp
 env env-entry
 archive archive-entry)


;;; Env Archive [Hash Nat [Dim U SVar]] [Hash SVar [Listof Nat]] [Listof [Set Nat]]
;;; -> [List Env Archive] U #f
(define (update-env env archive id->idx sym->id-list id-eqv-reln)
  #;(printf "(update-env\n ~v\n ~v\n ~v\n ~v\n ~v)\n\n"
            env archive id->idx sym->id-list id-eqv-reln)
  (define dim-eqv-reln
    (for/list ([id-eqv-class id-eqv-reln])
              ;; Convert each sequence component ID to a Remora index.
              (define new-class
                (for/list ([id id-eqv-class])
                          (define mapped (hash-ref id->idx id))
                          (if (hash? mapped)
                              (coeff-hash->dim mapped)
                              mapped)))
              ;; If everything in this equivalence class actually is a dim,
              ;; produce a list of dims. If it is a singleton class containing
              ;; a universal svar, produce an empty class. If it contains an
              ;; svar but is a non-singleton, produce #f as the equivalence
              ;; class to indicate an invalid equivalence class was given by
              ;; the sequence equation solver.
              (cond [(and (= 1 (length new-class))
                          (svar? (first new-class)))
                     '()]
                    [(for/or ([idx new-class]) (svar? idx)) #f]
                    [else new-class])))
  ;; If any equivalence class was marked as invalid, return #f.
  (and (for/and ([c dim-eqv-reln]) (list? c))
       ;; At this point, we know the equivalence relation only relates dims with
       ;; dims and universal shape variables with themselves.
       (let* ([sym->idx-list (translate-soln sym->id-list id->idx id-eqv-reln)]
              #;[_ (printf "Index solution structure:\n~v\n\n" sym->idx-list)]
              [env/dvars (resolve-dvars env dim-eqv-reln)]
              [env/svars (resolve-svars env/dvars sym->idx-list)]
              [archive/new-eqv-reln
                  (append (for/list ([dim-eqv-class dim-eqv-reln]
                                     #:unless (= 1 (length dim-eqv-class)))
                                    (cons '≐ dim-eqv-class))
                          archive)])
         (list env/svars archive/new-eqv-reln))))

;;; TODO: convert two Remora shapes into the form demanded by makanin/solve,
;;; invoke the solver, and generate updated environment for each result
;;; Env Archive Shp Shp -> [Stream [List Env Archive]]
(define (solutions env archive left right)
  (define univ-svars (set-union (list->set (unique-univ-svars left))
                                (list->set (unique-univ-svars left))))
  (define id-tables (id-numbers left right))
  (define id->coeff-hash (first id-tables))
  (define id->idx
    (for/hash ([(id hash-idx) id->coeff-hash])
              (values id (coeff-hash->dim hash-idx))))
  (define idx->id (second id-tables))
  #;(printf "SeqElt ID table:\n~v\n\n" (first id-tables))
  (define solns
    (solve-monoid-eqn*/t ((shp->sequence idx->id) left)
                         ((shp->sequence idx->id) right)))
  ;; Convert the equivalence relation on sequence element ID numbers into an
  ;; equivalence relation on syntactically encoded dims, and translate the
  ;; assignment so that its codomain is syntactic dims instead of ID numbers.
  ;; TODO: Try case where ^svar solution depends on later-bound ^dvars.
  ;; For example: [^@s, ..., ^$d, ^$e]  with ^@s resolved to one of {^$d, ^$e}
  ;; What substitution works for ^@s where ^$d and ^$e are not yet in scope?
  ;; Maybe add new exvar elements to the environment right before ^@s, similar
  ;; to refining the structure of a type as we discover how it is used? Then
  ;; instead of trying to produce something like
  ;;   [^@s ↦ {Shp ^$d ^$d}, ..., ^$d, ^$e ↦ ^$d]
  ;; we instead produce
  ;;   [^$f, ^@s ↦ {Shp ^$f ^$f}, ..., ^$d ↦ ^$f, ^$e ↦ ^$d]
  ;; As an exceptional case, if any position in an ex-svar's assignment is a
  ;; univ-svar that isn't in scope yet, then this is not a feasible solution
  ;; because it constrains a universal to have a particular value.
  ;; TODO: Consistency check for updated archive
  (define translated-solns
    (for/stream ([s solns])
                (define sym->id-list (first s))
                (define id-eqv-reln (second s))
                (update-env env archive id->idx sym->id-list id-eqv-reln)))
  translated-solns)
(module+ test
  (check-equal? (stream-first (solutions (term [(^ $x) (^ $y) (^ @s)])
                                         (term [])
                                         (term {Shp (^ $x) (^ $y)})
                                         (term {++ {Shp 5} (^ @s)})))
                '([(^ $x 5)
                   (^ $y)
                   (^ @s (Shp (^ $y)))]
                  [(≐ (^ $x) 5)])))

;;; Translate shp from redex's representation into makanin/solve representation
(define ((shp->sequence ids) s)
  (match s
    [(? svar? x) (list (hash-ref ids s))]
    [(list '^ x) (list x)]
    [(list 'Shp dims ...) (map (dim->sequence-elt ids) dims)]
    [(list '++ shps ...) (apply append (map (shp->sequence ids) shps))]))
(define ((dim->sequence-elt ids) d)
  (hash-ref ids (dim->coeff-hash d)))

;;; Identify all dimensions appearing in a shp
(define (unique-dims s)
  (define (shp->dim-list s)
    (match s
      [(or (? svar? x) (list '^ x)) '()]
      [{list 'Shp dims ...} dims]
      [{list '++ shps ...} (apply append (map shp->dim-list shps))]))
  (remove-duplicates (shp->dim-list s)
                     (λ (l r) (equal? (dim->coeff-hash l)
                                      (dim->coeff-hash r)))))

;;; Identify all universal shape variables appearing in a shp
(define (shp->univ-svar-list s)
  (match s
    [(? svar? x) (list s)]
    [(list '^ x) '()]
    [{list 'Shp dims ...} '()]
    [{list '++ shps ...} (apply append (map shp->univ-svar-list shps))]))
(define (unique-univ-svars s)
  (remove-duplicates (shp->univ-svar-list s)))

;;; Given a shape equation, pick ID numbers for each distinct dimension and
;;; each universal shape variable. Construct hashes mapping between ID numbers
;;; and their referents.
;;; Shp Shp -> [List [Hash Natural CoeffHash] [Hash CoeffHash Natural]]
(define (id-numbers left right)
  (define dims (unique-dims (list '++ left right)))
  (define dim-mapping (for/list ([n (in-naturals 0)]
                                 [d dims])
                                #;(printf "Represent ~v as ~v\n" d n)
                                (list n (dim->coeff-hash d))))
  (define svars (unique-univ-svars (list '++ left right)))
  (define svar-mapping (for/list ([n (in-naturals (length dim-mapping))]
                                  [v svars])
                                 #;(printf "Represent ~v as ~v\n" v n)
                                 (list n v)))
  (define idx-mapping (append dim-mapping svar-mapping))
  (list (for/hash ([pair idx-mapping])
                  (values (first pair) (second pair)))
        (for/hash ([pair idx-mapping])
                  (values (second pair) (first pair)))))

;;; Wrapper around resolve-dvars/rev, described below
(define (resolve-dvars env eqv-reln)
  (reverse (resolve-dvars/rev (reverse env) (set) eqv-reln)))

;;; Given a reversed environment and an equivalence relation on dims, produce a
;;; new version of the environment which resolves existential dvars mentioned in
;;; the equivalence relation to linear combinations of dvars which appear
;;; earlier in the environment. Keep track of the later-bound dvars to ensure
;;; there are no forward references in the resulting environment. The result
;;; environment is also reversed.
;;; Remora-elab:env [Set Remora-elab:dvar] [Listof [Set Remora-elab:dim]]
;;; -> Remora-elab:env
(define (resolve-dvars/rev rev-env forbidden-dvars eqv-reln)
  (match rev-env
    ['() '()]
    ;; This exvar is already resolved. Add it to the forbidden set and recur.
    [(cons (list '^ (? dvar? d) (? dim? _)) rest-env)
     (cons (first rev-env)
           (resolve-dvars/rev rest-env
                              (set-add forbidden-dvars (list '^ d))
                              eqv-reln))]
    ;; A universal variable is not resolvable.
    [(cons (? dvar? d) rest-env)
     (cons d (resolve-dvars/rev rest-env
                                (set-add forbidden-dvars d)
                                eqv-reln))]
    ;; Search the equivalence relation for a solution. Add the result into the
    ;; environment, and recur on the rest, forbidding this exvar.
    [(cons (list '^ (? dvar? d)) rest-env)
     #;(printf "Can we pick an answer for ~v?\n" d)
     (cons (resolve-dvar (first rev-env) forbidden-dvars eqv-reln)
           (resolve-dvars/rev rest-env
                              (set-add forbidden-dvars (list '^ d))
                              eqv-reln))]
    ;; Other environment entries do not affect this process.
    [(cons _ rest-env)
     (cons (first rev-env)
           (resolve-dvars/rev rest-env forbidden-dvars eqv-reln))]))

;;; Does this dimension mention the variable?
(define (mentions? dvar dim)
  (match dim
    [(? (λ (x) (equal? x dvar)) _) #t]
    [(list (or '+ '-) dim ...) (for/or ([dim dim]) (mentions? dvar dim))]
    [_ #f]))
(module+ test
  (check-true (mentions? (term $x) (term {+ 3 $y {- $x $x}})))
  (check-true (mentions? (term $y) (term {+ 3 $y {- $x $x}})))
  (check-false (mentions? (term $z) (term {+ 3 $y {- $x $x}})))
  (check-false (mentions? (term (^ $x)) (term {+ 3 $y {- $x $x}})))
  (check-false (mentions? (term $z) (term {+ 3 $y {- (^ $z) $x}})))
  (check-true (mentions? (term (^ $z)) (term {+ 3 $y {- (^ $z) $x}}))))

;;; What variables does this dimension mention?
;;; dim -> [Set [dvar U exdvar]]
(define (dim-vars dim)
  (match dim
    [(? (disjoin dvar? exdvar?) d) (set d)]
    [(? number? _) (set)]
    [(list (or '+ '- '* '/) dims ...)
     (apply set-union (set) (map dim-vars dims))]))

;;; What coefficient does the given variable have when the dim is viewed as an
;;; affine combination of variables?
(define (coefficient x dim)
  (if (number? x)
      (const-component dim)
      (var-coefficient x dim)))
(define (const-component dim)
  (match dim
    [(? (disjoin dvar? exdvar?) d) 0]
    [(? number? d) d]
    [(list '+ dim ...) (apply + (map const-component dim))]
    [(list '- dim ...) (apply - (map const-component dim))]
    [(list '* dim ...) (apply * (map const-component dim))]
    [(list '/ dim ...) (apply / (map const-component dim))]))
(define (var-coefficient dvar dim)
  (match dim
    [(? (disjoin dvar? exdvar?) d)
     (if (equal? dvar d) 1 0)]
    [(? number? d) 0]
    [(list '+ dim ...)
     (apply + (map (λ (subterm) (var-coefficient dvar subterm)) dim))]
    [(list '- dim ...)
     (apply - (map (λ (subterm) (var-coefficient dvar subterm)) dim))]
    [(list '* nat dim)
     (* nat (var-coefficient dvar dim))]
    [(list '/ dim nat)
     (/ (var-coefficient dvar dim) nat)]))
(module+ test
  (check-equal? (coefficient (term $x) (term {+ 3 $y {+ $x $x}})) 2)
  (check-equal? (coefficient (term (^ $x)) (term {+ 3 $y {+ $x $x}})) 0)
  (check-equal? (coefficient (term (^ $x)) (term {+ 3 (^ $y) {+ $x $x}})) 0)
  (check-equal? (coefficient (term (^ $x)) (term {+ 3 (^ $x) {+ (^ $x) $x}})) 2)
  (check-equal? (coefficient (term $y) (term {+ 3 $y {+ $x $x}})) 1)
  (check-equal? (coefficient (term $z) (term {+ 3 $y {+ $x $x}})) 0)
  (check-equal? (coefficient (term $x) (term {+ 3 $y {- $x $x}})) 0)
  (check-equal? (coefficient (term $x) (term {+ 3 $y {- $z $x}})) -1)
  (check-equal? (coefficient 1 (term {+ 13 $y {- $z 15}})) -2))

;;;; Tools for simplifying a dimension

;;; Convert a syntactic dim to a coefficient hash representation
(define (dim->coeff-hash dim)
  (for/hash ([d (set-add (dim-vars dim) 1)]) (values d (coefficient d dim))))

(define ((coeff-hash-binop op) left right)
  (define dvars (set-union (list->set (hash-keys left))
                           (list->set (hash-keys right))))
  (for/hash ([d (set-add dvars 1)]
             #:unless (= 0 (op (hash-ref left d 0)
                               (hash-ref right d 0))))
            (values d (op (hash-ref left d 0)
                          (hash-ref right d 0)))))
(define ((coeff-hash-unop op) h)
  (define dvars (list->set (hash-keys h)))
  (for/hash ([d (set-add dvars 1)]
             #:unless (= 0 (op (hash-ref h d 0))))
            (values d (op (hash-ref h d 0)))))

;;; Convert a coefficient hash back to a somewhat pretty-printed syntactic dim
(define (coeff-hash->dim coeffs)
  #;(printf "Converting ~v\n" coeffs)
  (define common-denominator
    (apply lcm (for/list ([c (hash-values coeffs)]
                          #:unless (zero? c))
                         (denominator c))))
  (define (component->dim comp)
    (match (length comp)
      [0 0]
      [1 (first comp)]
      [_ (cons '+ comp)]))
  (define positives
    (component->dim
     (for/fold ([elts '()])
               ([(d coeff) coeffs]
                #:when (> coeff 0))
       (define adj-coeff (* common-denominator coeff))
       (if (number? d)
           (cons adj-coeff elts)
           (cons (if (= 1 adj-coeff) d (list '* adj-coeff d))
                 elts)))))
  (define negatives
    (component->dim
     (for/fold ([elts '()])
               ([(d coeff) coeffs]
                #:when (< coeff 0))
       (define adj-coeff (* common-denominator coeff -1))
       (if (number? d)
           (cons adj-coeff elts)
           (cons (if (= 1 adj-coeff) d (list '* adj-coeff d))
                 elts)))))
  (define subtracted
    (cond
      [(equal? 0 negatives) positives]
      [(equal? 0 positives)
       (if (list? negatives) (cons '- (cons 0 (rest negatives)))
           (list '- 0 negatives))]
      [else (list '- positives negatives)]))
  (cond [(= 1 common-denominator) subtracted]
        [else (list '/ subtracted common-denominator)]))

;;; A coefficient hash should be unchanged by a round trip through syntactic
;;; representation, though a syntactic dim may change.
(module+ test
  (check-true
   (redex-check
    Remora-elab dim
    (equal? (dim->coeff-hash (term dim))
            (dim->coeff-hash (coeff-hash->dim (dim->coeff-hash (term dim)))))
    #:print? #f)))

;;; Isolate a chosen variable in an equality
(define (isolate dvar left right)
  (define lhs (dim->coeff-hash left))
  (define rhs (dim->coeff-hash right))
  (define lhs-coeff (hash-ref lhs dvar 0))
  (define rhs-coeff (hash-ref rhs dvar 0))
  ;; LHS - RHS = 0, and dvar's coeff will be (lhs-coeff - rhs-coeff)
  ;; Dividing by (rhs-coeff - lhs-coeff) gives a version
  ;; where dvar's coeff is -1.
  (define soln-hash
   ((coeff-hash-binop +)
    (hash dvar 1)
    ((coeff-hash-unop (λ (x) (/ x (- rhs-coeff lhs-coeff))))
     ((coeff-hash-binop -) lhs rhs))))
  (coeff-hash->dim soln-hash))

;;; Use an equivalence relation to find a way to rewrite a dimension variable
;;; in terms of other dimension variables not marked as "forbidden."
;;; ExDimVar [Set DimVar] [Listof [Set Dim]] -> [List '^ DimVar Dim]
(define (resolve-dvar dvar forbidden-dvars eqv-reln)
  ;; Find a specific equation to use. This must be two dimensions in the same
  ;; equivalence class which have differing coefficients for dvar and equal
  ;; coefficients for each forbidden variable. If no such equation is available,
  ;; return #f.
  #;(printf "\tUsing equivalence relation ~v\n" eqv-reln)
  (define (eqv-class->eqn eqv-class)
    (or (set-empty? eqv-class)
        (let ([lhs (set-first eqv-class)])
          (for/first ([rhs (set-rest eqv-class)]
                      #:when (and (not (= (coefficient dvar lhs)
                                          (coefficient dvar rhs)))
                                  (for/and ([fv forbidden-dvars])
                                           (= (coefficient fv lhs)
                                              (coefficient fv rhs)))))
                     (list lhs rhs)))))
  (define found-equality
    (for/first ([eqv-class eqv-reln]
                #:when (eqv-class->eqn eqv-class))
               (eqv-class->eqn eqv-class)))
  #;(printf "\tFound equality: ~v\n" found-equality)
  (if found-equality
      ;; With the two sides of the equation rewritten as coefficient hashes,
      ;; isolate the chosen variable.
      `(^ ,(second dvar) ,(isolate dvar (first found-equality) (second found-equality)))
      `(^ ,(second dvar))))


;;; Similar to resolve-dvar, but for resolving shape variables. The solver's
;;; shape solution is a hash which maps shape variables to sequences of element
;;; IDs. Each element ID might mean any one of several dimensions, as specified
;;; by the associated equivalence relation returned by the solver.
;;; TODO: If all dims in the eqv class specified for some position mention an
;;; exvar that is out of scope, we can introduce a new one immediately before
;;; this shape exvar. This will rely on some other code to filter out cases
;;; where the equivalence relation has a term using an exvar equated with a
;;; term using a later-bound univar.
;;; SVar
;;; [Hash SVar [Listof Nat]]
;;; [Listof [Set Nat]]
;;; [Hash Nat Dim]
;;; [Listof DVar]
;;; -> [[Listof Shp] U #f]
#;
(define (resolve-svar svar svar-subst id-eqv-reln id->dim forbidden-vars)
  (define positional-solutions
    (for/list ([dim-id (hash-ref svar-subst svar '())])
              ;; Identify the equivalence class of dim ID numbers that contains
              ;; dim-id, and pick one from that class which stands for a dim
              ;; which uses no forbidden variables.
              (define id-eqv-class
                (for/first ([c id-eqv-reln] #:when (set-member? c dim-id)) c))
              (define dim-eqv-class
                (for/list ([id id-eqv-class]) (hash-ref id->dim id)))
              (for/first
                   ([dim dim-eqv-class]
                    #:when (for/and ([fv forbidden-vars])
                                    (not (mentions? fv dim))))
                   dim)))
  ;; If every position has a solution, return that list of solutions. Ohherwise,
  ;; return false.
  (if (for/and ([s positional-solutions]) s)
      positional-solutions
      #f))

;;; For each position in an SVar's solution, choose a candidate index which does
;;; not mention any forbidden variables. If no such solution is available for
;; some component, return #f.
;;; [Set Var] [Listof [Set Shp]] -> Shp U #f
(define (resolve-svar forbidden-vars components)
  (define specific-pieces
    (for/list ([c components])
              #;(printf "Possibilities: ~v\n" c)
              (for/first ([s c]
                          #:when (set-empty? (set-intersect (shp->ivars s)
                                                            forbidden-vars)))
                         s)))
  #;(printf "Specific pieces: ~v\n" specific-pieces)
  (and (for/and ([s specific-pieces]) s)
       specific-pieces))

;;; Construct the set of index variables mentioned in a shape
;;; Shp -> [Set IVar]
(define (shp->ivars s)
  (match s
    [(or (? svar? _) (list '^ (? svar? _))) (set s)]
    [(list 'Shp dims ...) (apply set-union (set) (map dim->dvars dims))]
    [(list '++ shps ...) (apply set-union (set) (map shp->ivars shps))]))

;;; Construct the set of index variables mentioned in a dimension
;;; Dim -> [Set DVar]
(define (dim->dvars d)
  (match d
    [(or (? dvar? _) (list '^ (? dvar? _))) (set d)]
    [(? natural? _) (set)]
    [(list '+ dims ...) (apply set-union (set) (map dim->dvars dims))]))


;;; In a reversed environment, resolve all svars that have a solution in the
;;; given solution hash, subject to the chosen equivalence relation on dimension
;;; IDs and mapping from IDs to dimensions.
;;; Env [Hash SVar [Listof Shp]] [Set IVar] [Kont Bool]
;;; -> Env U #f
(define (resolve-svars/rev rev-env forbidden-vars svar->idx-list bailout)
  (match rev-env
    ['() '()]
    ;; Resolved existential variable: add to forbidden set
    [(cons (list '^ (? ivar? v) (? idx? _)) rest-env)
     (cons (first rev-env)
           (resolve-svars/rev rest-env
                              (set-add forbidden-vars (list '^ v))
                              svar->idx-list
                              bailout))]
    ;; Universal variable: add to forbidden set
    [(cons (? ivar? v) rest-env)
     (cons v (resolve-svars/rev rest-env
                                (set-add forbidden-vars v)
                                svar->idx-list
                                bailout))]
    ;; Unresolved dimension variable: add to forbidden set
    [(cons (list '^ (? dvar? v)) rest-env)
     (cons (first rev-env)
           (resolve-svars/rev rest-env
                              (set-add forbidden-vars (list '^ v))
                              svar->idx-list
                              bailout))]
    ;; Unresolved shape variable: try to solve it
    [(cons (list '^ (? svar? v)) rest-env)
     #;(printf "Try to resolve ~v\n" (first rev-env))
     (define component-solns (hash-ref svar->idx-list v #f))
     #;(printf "  Components' candidate solutions: ~v\n" component-solns)
     (define shp-soln
       (if component-solns (resolve-svar forbidden-vars component-solns) '()))
     (if shp-soln
         (cons (append (first rev-env) shp-soln)
               (resolve-svars/rev rest-env
                                  (set-add forbidden-vars (list '^ v))
                                  svar->idx-list
                                  bailout))
         ;; If there was no scope-respecting solution for any existential shape
         ;; variable, then we cannot use this candidate solution.
         (bailout #f))]
    ;; Otherwise: ignore
    [(cons _ rest-env)
     (cons (first rev-env) (resolve-svars/rev rest-env
                                              forbidden-vars
                                              svar->idx-list
                                              bailout))]))
;;; Given the shapes each component of an existential shape var might stand for,
;;; pick for each position a shape which mentions only variable that are in
;;; scope when the existential is bound.
;;; Env [Hash SVar [List Shp]] -> Env U #f
(define (resolve-svars env svar->idx-list)
  (let/ec bailout
    (reverse (resolve-svars/rev (reverse env) (set) svar->idx-list bailout))))

;;; Convert a solution which maps existential shape variables to component IDs
;;; into a solution which maps them to sets of indices.
;;; [Hash SVar [Listof Nat]]
;;; [Hash Nat Idx]
;;; [Listof [Set Nat]]
;;; -> [Hash SVar [Listof [Set Shp]]
(define (translate-soln id-soln id->idx id-eqv-reln)
  (for/hash
   ([(svar ids) id-soln])
   (values
    svar
    (for/list ([id ids])
              ;; Find the equivalence class that contains this ID
              (define eqv-class
                (for/first ([c id-eqv-reln] #:when (set-member? c id)) c))
              (for/set ([id eqv-class])
                       (define mapped-val (hash-ref id->idx id))
                       (if (svar? mapped-val)
                           mapped-val
                           `(Shp ,mapped-val)))))))
