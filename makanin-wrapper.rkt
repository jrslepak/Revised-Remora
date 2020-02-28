#lang racket

(require redex
         makanin/solve
         "language.rkt"
         "implicit-lang.rkt"
         (except-in "elab-lang.rkt" Scl scl)
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
  (define dim-eqv-reln
    (for/list ([id-eqv-class id-eqv-reln])
              ;; Convert each sequence component ID to a Remora index.
              (define new-class
                (for/set ([id id-eqv-class])
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
              (cond [(and (= 1 (set-count new-class))
                          (svar? (set-first new-class)))
                     (set)]
                    [(for/or ([idx new-class]) (svar? idx)) #f]
                    [else new-class])))
  ;; If any equivalence class was marked as invalid, return #f.
  (and (for/and ([c dim-eqv-reln]) (set? c))
       ;; At this point, we know the equivalence relation only relates dims with
       ;; dims and universal shape variables with themselves.
       (let* ([sym->idx-list (elaborate-svars sym->id-list id->idx)]
              [env/elaborated (elaborate-exsvar-entries env sym->idx-list)]
              [dim-eqv-reln/fresh-dvars
               (for/fold ([eqv dim-eqv-reln])
                         ([svar (hash-keys sym->idx-list)])
               (augment-eqv-reln eqv
                                 (hash-ref sym->idx-list svar)
                                 (hash-ref sym->id-list svar)
                                 id->idx))]
              [env/dvars (resolve-dvars env/elaborated dim-eqv-reln/fresh-dvars)]
              [archive/new-eqv-reln
                  (append (for/list ([dim-eqv-class dim-eqv-reln/fresh-dvars]
                                     #:unless (= 1 (set-count dim-eqv-class)))
                                    (cons '≐ (set->list dim-eqv-class)))
                          archive)])
         (list env/dvars archive/new-eqv-reln))))

;;; Generate fresh existential dimension variables for positions in a solved
;;; existential shape variable which correspond to single dimensions, and leave
;;; positions corresponding to universal shape variables as those variables.
;;; [Hash SVar [Listof Nat]] [Hash Nat [Dim U Svar]]
;;; -> [Listof Shp]
(define (elaborate-svars sym->id-list id->idx)
  #;(printf "Elaborating solution:\n~v\n~v\n\n" sym->id-list id->idx)
  (for/hash
   ([(svar _) sym->id-list])
   (values
    svar
    (for/list
     ([component-id (hash-ref sym->id-list svar '())]
      [i (in-naturals)])
     ;; TODO: What if this component is unconstrained so the hash contains #f?
     ;; For now, treating any unconstrained position as a 0 dimension.
     (cond [(not component-id) '{Shp 0}]
           [(svar? (hash-ref id->idx component-id))
            (hash-ref id->idx component-id)]
           [else
            `(Shp (^ ,(string->symbol (format
                                       "$~a~a"
                                       (substring
                                        (symbol->string svar) 1) i))))])))))

;;; For each svar in the given solution hash, elaborate piece of the environment
;;; to include entries for the newly-generated ^dvar components.
;;; Env [Hash SVar [Listof Shp]] -> Env
(define (elaborate-exsvar-entries env sym->idx-list)
  (match env
    [(cons (list '^ (? svar? svar)) rest-env)
     (define new-entries
       (for/list ([component (hash-ref sym->idx-list svar '())]
                  #:when (and (list? component)
                              (> (length component) 1)
                              (exdvar? (second component))))
                 (second component)))
     (append new-entries
             (list
              (if (hash-has-key? sym->idx-list svar)
                  `(^ ,svar ,(term (Inormalize-idx
                                    ,(cons '++ (hash-ref sym->idx-list svar)))))
                  `(^ ,svar)))
             (elaborate-exsvar-entries rest-env sym->idx-list))]
    [(cons env-entry rest-env)
     (cons env-entry (elaborate-exsvar-entries rest-env sym->idx-list))]
    ['() '()]))

;;; Expand the equivalence class for each component id mentioned in the shape
;;; variable's solution to include the existential dimension variable generated
;;; for the corresponding position.
;;; [Listof [Set Remora-elab:dim]] [Listof Shp] [Listof Nat] [Hash Nat [Dim U SVar]]
;;; -> [Listof [Set Nat]]
(define (augment-eqv-reln dim-eqv-reln fresh-components component-ids id->idx)
  ;; Update each equivalence class. If an element ID which appears at the same
  ;; position within component-ids where an existential dimension variable
  ;; appears within fresh-components, and the index corresponding to that ID is
  ;; already in this equivalence class, then include the fresh ^dvar in this
  ;; class as well.
  (for/list
   ([eqv-class dim-eqv-reln])
   (define new-elements
     (for/set ([fc fresh-components]
               [id component-ids]
               #:when (and (list? fc)
                           (> (length fc) 1)
                           (exdvar? (second fc))
                           (set-member? eqv-class (hash-ref id->idx id #f))))
              (second fc)))
   (set-union eqv-class new-elements)))

;;; Convert two Remora shapes into the form demanded by makanin/solve,
;;; invoke the solver, and generate updated environment for each result.
;;; Env Archive Shp Shp -> [Stream [List Env Archive]]
(define (solutions env archive left right)
  (define univ-svars (set-union (list->set (unique-univ-svars left))
                                (list->set (unique-univ-svars left))))
  (define id-tables (id-numbers left right))
  (define id->coeff-hash (first id-tables))
  (define id->idx
    (for/hash ([(id hash-idx) id->coeff-hash])
              (values id
                      (if (hash? hash-idx)
                          (coeff-hash->dim hash-idx)
                          hash-idx))))
  (define idx->id (second id-tables))
  (define solns
    (solve-monoid-eqn*/t ((shp->sequence idx->id) left)
                         ((shp->sequence idx->id) right)))
  ;; Convert the equivalence relation on sequence element ID numbers into an
  ;; equivalence relation on syntactically encoded dims, and translate the
  ;; assignment so that its codomain is syntactic dims instead of ID numbers.
  (define translated-solns
    (for/stream ([s solns])
                (define sym->id-list (first s))
                (define id-eqv-reln (second s))
                (update-env env archive id->idx sym->id-list id-eqv-reln)))
  (for/stream ([candidate translated-solns]
               ;; TODO: Consistency check for updated archive
               ;;  - Make sure (mixed-prefix?) ILP for dims in archive is SAT
               ;;    - Disallow exvar depending on later univar
               ;;    - Need to be able to build a concrete solution for exvars
               ;;  - If ILP is UNIQUE-SAT, propagate the sole solution?
               #:when (failure-free? (first candidate)))
              candidate))
(module+ test
  (check-equal? (stream->list (solutions '[] '[] '{Shp} '{Shp}))
                '(([] [])))
  (check-equal? (stream->list (solutions '[] '[] '{Shp 4} '{Shp 4}))
                '(([] [])))
  (check-equal? (stream->list (solutions '[(^ @s)] '[] '(^ @s) '{Shp}))
                '(([(^ @s (Shp))]
                   [])))
  (check-equal? (stream->list (solutions '[(^ @s)] '[] '(^ @s) '{Shp 5}))
                '(([(^ $s0 5)
                    (^ @s (Shp (^ $s0)))]
                   [(≐ (^ $s0) 5)])))
  (check-equal? (stream->list (solutions '[@s] '[] '@s '{Shp}))
                '())
  (check-equal? (stream-first (solutions (term [(^ $x) (^ $y) (^ @s)])
                                         (term [])
                                         (term {Shp (^ $x) (^ $y)})
                                         (term {++ {Shp 5} (^ @s)})))
                '([(^ $x 5)
                   (^ $y)
                   (^ $s0 (^ $y))
                   (^ @s (Shp (^ $s0)))]
                  [(≐ (^ $y) (^ $s0))
                   (≐ (^ $x) 5)]))
  (check-equal? (stream-first (solutions (term [(^ @s) (^ $n)])
                                         (term [])
                                         (term (^ @s))
                                         (term {Shp (^ $n)})))
                '([(^ $s0) (^ @s {Shp (^ $s0)}) (^ $n (^ $s0))]
                  [(≐ (^ $n) (^ $s0))]))
  (check-equal? (stream-first (solutions (term [(^ @s) (^ $n)])
                                         (term [])
                                         (term (^ @s))
                                         (term {Shp (^ $n) (^ $n)})))
                '([(^ $s0) (^ $s1 (^ $s0)) (^ @s {Shp (^ $s0) (^ $s1)}) (^ $n (^ $s1))]
                  [(≐ (^ $n) (^ $s0) (^ $s1))]))
  ;; Mixing universal and existential variables should only work if existentials
  ;; are resolved as earlier-bound universals. If they depend on later-bound
  ;; universals, then no solution is possible.
  (check-equal? (stream->list (solutions '[(^ $x) $l] '[] '{Shp (^ $x)} '{Shp $l}))
                '())
  (check-equal? (stream->list (solutions '[$l (^ $x)] '[] '{Shp (^ $x)} '{Shp $l}))
                '(([$l (^ $x $l)]
                   [(≐ (^ $x) $l)]))))

;;; Check whether an environment contains any existentials resolved as 'FAILURE.
(define (failure-free? env)
  (match env
    [(cons (list '^ _ 'FAILURE) _) #f]
    [(cons _ rest-env) (failure-free? rest-env)]
    ['() #t]))


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

;;; Convert a solution which maps existential shape variables to component IDs
;;; into a solution which maps them to sets of indices.
;;; [Hash SVar [Listof Nat]]
;;; [Hash Nat Idx]
;;; [Listof [Set Nat]]
;;; -> [Hash SVar [Listof [Set Shp]]
(define (translate-soln id-soln id->idx id-eqv-reln)
  (for/hash
   ([(svar ids) id-soln]
    #:when (for/and ([id ids]) id))
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

;;; Wrapper around resolve-dvars/rev, described below
(define (resolve-dvars env eqv-reln)
  (reverse (resolve-dvars/rev (reverse env) (set) eqv-reln)))

;;; TODO: For each unsolved exdvar d mentioned in an equivalence relation, find
;;; a lower bound based on the dims it's related to. Each equality involving d
;;; when solved for d gives a constant component k. If k>0, insert a fresh
;;; exdvar d' in the environment before d, and solve d as d'+k.

;;; Given a reversed environment and an equivalence relation on dims, produce a
;;; new version of the environment which resolves existential dvars mentioned in
;;; the equivalence relation to linear combinations of dvars which appear
;;; earlier in the environment. Keep track of the later-bound dvars to ensure
;;; there are no forward references in the resulting environment. The result
;;; environment is also reversed.
;;; Remora-elab:env [Set Remora-elab:dvar] [Listof [Set Remora-elab:dim]]
;;; -> [Listof [Remora-elab:env-entry U (^ DimVar 'FAILURE)]]
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
    ;; TODO: If anything in the equivalence relation mentions a forbidden
    ;; universal variable, this entire solution should be rejected.
    [(cons (list '^ (? dvar? d)) rest-env)
     (cons (resolve-dvar (first rev-env) forbidden-dvars eqv-reln)
           (resolve-dvars/rev rest-env
                              (set-add forbidden-dvars (list '^ d))
                              eqv-reln))]
    ;; Other environment entries do not affect this process.
    [(cons _ rest-env)
     (cons (first rev-env)
           (resolve-dvars/rev rest-env forbidden-dvars eqv-reln))]))

;;; Use an equivalence relation to find a way to rewrite a dimension variable
;;; in terms of other dimension variables not marked as "forbidden."
;;; ExDimVar [Set DimVar] [Listof [Set Dim]]
;;; -> [List '^ DimVar [Dim U 'FAILURE]] U [List '^ DimVar]
(define (resolve-dvar dvar forbidden-dvars eqv-reln)
  ;; Find a specific equation to use. This must be two dimensions in the same
  ;; equivalence class which have differing coefficients for dvar and equal
  ;; coefficients for each forbidden variable. If no such equation is available,
  ;; return #f.
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
  ;; If dvar shares an equivalence class with any term mentioning a forbidden
  ;; universal variable, we must return 'FAILURE as dvar's solution.
  (define forbidden-uvar?
    (for/or ([eqv-class eqv-reln])
            (and
             ;; Does this eqv class mention dvar?
             (for/or ([dim eqv-class]) (mentions? dvar dim))
             ;; Are any universals mentioned by this eqv class forbidden?
             (for/or ([dim eqv-class])
                     (define bad-uvars
                       (set-intersect
                        (for/set ([f (dim-vars dim)] #:when (dvar? f)) f)
                        (for/set ([f forbidden-dvars] #:when (dvar? f)) f)))
                     (not (set-empty? bad-uvars))))))
  (define found-equality
    (for/first ([eqv-class eqv-reln]
                #:when (eqv-class->eqn eqv-class))
               (eqv-class->eqn eqv-class)))
  (cond [forbidden-uvar? `(^ ,(second dvar) FAILURE)]
        [found-equality
         ;; With the two sides of the equation rewritten as coefficient hashes,
         ;; isolate the chosen variable.
         `(^ ,(second dvar)
             ,(isolate dvar (first found-equality)
                       (second found-equality)))]
        [else `(^ ,(second dvar))]))


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


;;;;----------------------------------------------------------------------------
;;;; Tools for simplifying a dimension
;;;;----------------------------------------------------------------------------

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
    Remora-implicit dim
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
