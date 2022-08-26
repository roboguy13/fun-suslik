#lang racket

(require redex)
(require racket/set)

(define-language fun-SuSLik
  (data-def ::= (data D where alt ...))
  (alt ::= (C τ ...))
  (τ ::= Int Bool (τ → τ) D)
  (Γ ::= · (extend Γ (x : τ)) (extend Γ L layout-fn-def))
  ;(Σ ::= · (extend Σ layout-fn-def))
  (fn-def ::= ((f : τ) (fn-case ...)))
  (fn-case ::= (pat guarded-expr guarded-expr ...))
  #;(guard ::= (bool-expr ...))
  (guarded-expr ::= [bool-expr → e])
  #;(match-expr ::= (match e match-cases))
  (match-case ::= (pat → e))
  (match-cases ::= match-case (match-case match-cases))
  (layout-fn-def ::= ((L : τ >-> layout [ x ... ]) layout-cases))
  (layout-case ::= ([x ...] pat → fs-assertion))
  (layout-cases ::= layout-case (layout-case layout-cases))
  (fs-heaplet κ ::= emp (p :-> pointed-to) (p = equals-val) layout-app)
  (fs-heaplet-val ::= emp (p :-> pointed-to) (p = equals-val) (L [x ...] pointed-to))
  (equals-val ::= 0 x)
  (layout-app ::= (L [x ...] layout-arg))
  (fs-assertion ::= (fs-heaplet ...))
  (lower-app (lower [x ...] L e))
  (layout-arg ::= y constr-app lower-app)
  (pat ::= C (C x ...))
  (p ::= x (x + n))
  (n ::= natural)
  (I ::= integer)
  (B ::= false true)
  (pointed-to ::= base-val x)
  (base-val ::= integer B)
  (params ::= [x ...])
  (constr-app ::= C (C e ...))
  (compose-arg ::= x ?)
  (compose-arg* ::= compose-arg compose-app)
  (compose-app ::=
               (f compose-arg ...)
               (lower [] L (C compose-arg ...)))
  (compose-app* ::=
                (f compose-arg* ...)
                (lower [] L (C compose-arg* ...)))
  (bool-expr ::= B x
             (&& bool-expr ...) (|| bool-expr ...) (not bool-expr)
             (== pointed-to pointed-to)
             (<= pointed-to pointed-to)
             (< pointed-to pointed-to))
  (e ::= x I B (e_1 e_2 ...) (λ (a : τ) → e) (let x := e_1 in e_2) (e_1 e_2) builtin)
  (builtin ::= ite < <= == + - && || not lower-app (lift [x ...] L e))
  (D a b f g h x y z i j k ::= variable-not-otherwise-mentioned)
  (L ::= (variable-prefix L-))
  (C ::= (variable-prefix C-))
  (pred-name ::= (variable-prefix L-pred-))

  (fs-heaplet-applied ::= fs-heaplet (fs-heaplet-applied ...))
  (fs-assertion-applied ::= (fs-heaplet-applied ...))

  (fs-heaplet-val-applied ::= fs-heaplet-val (fs-heaplet-val-applied ...))

  (layout-case-hole ::= ([x ...] pat → fs-assertion-hole))
  (fs-assertion-hole ::= hole #;(fs-heaplet fs-assertion-hole fs-heaplet ...)
                     (fs-heaplet-val-applied ... fs-assertion-hole fs-heaplet-applied ...)
                     #;(fs-heaplet ... fs-assertion-hole))

  (flatten-assertion-applied ::= hole #;(fs-heaplet-applied flatten-assertion-applied fs-heaplet-applied ...)
                             (fs-heaplet ... flatten-assertion-applied fs-heaplet-applied ...)
                             #;(fs-heaplet-val-applied ... flatten-assertion-applied))

  (value ::= base-val C (C value ...))

  (lowered ::= value (lower [x ...] L value))
  (lifted ::= value (lift [x ...] L value))
  (instantiate-e ::= hole
           (instantiate-e e ...)
           (lower [x ...] L instantiate-e)
           #;(C lowered ... e-lower e ...)
           (lower [x ...] L (f lifted ... instantiate-e e ...))
           #;(lower L (match lifted match-cases)))

  (suslik-predicate ::=
                    (inductive pred-name (y ...) pred-branch ...))
  (pred-branch ::= (pure-part ⇒ suslik-assertion))
  (suslik-heaplet ::= emp (p :-> pointed-to) (func f x ...) (L x ...) (L [x ...] y ...) (x = equals-val))
  (suslik-heaplets ::= (suslik-heaplet ...))
  (suslik-assertion ::= (pure-part (suslik-heaplet ...)))
  (suslik-assertions ::= (suslik-assertion ...))
  (pure-part ::= bool-expr)
  (int-expr ::=
            x
            integer
            (int-expr + int-expr)
            (int-expr - int-expr)
            (int-expr * int-expr))
  #;(bool-expr ::=
             x
             boolean
             (and bool-expr bool-expr)
             (or bool-expr bool-expr)
             (not bool-expr)
             (le int-expr int-expr)
             (equal int-expr int-expr))
  (suslik-spec ::= (suslik-assertion suslik-assertion))

  #:binding-forms
  (λ (x : τ) → e #:refers-to x)
  (let x := e_1 in e_2 #:refers-to x)
  (((f_1 : τ) ((C x ...) guard → e #:refers-to (shadow x ...)) ...))
  ([x ...] (C y ...) → fs-assertion #:refers-to (shadow x ... y ...))
  (inductive pred-name (y ...) (pred-branch ...) #:refers-to (shadow y ...)))

(define-metafunction fun-SuSLik
  different : x y -> boolean
  [(different x x) #f]
  [(different x y) #t])

(define-judgment-form fun-SuSLik
  #:mode (lookup I I O)
  ;#:contract (lookup Γ x τ)
  [-------------------
   (lookup (extend Γ (x : τ)) x τ)]

  [(lookup Γ x τ)
   (where #t (different x y))
   -------------------
   (lookup (extend Γ (y : τ_2)) x τ)]

  [-------------------
   (lookup (extend Γ L layout-fn-def) L layout-fn-def)]

  [(lookup Γ L layout-fn-def)
   (where #t (different L_2 L))
   ------------------
   (lookup (extend Γ L_2 layout-fn-def_2) L layout-fn-def)
   ])


(define-judgment-form fun-SuSLik
  #:contract (has-type Γ e τ)
  #:mode (has-type I I O)
  [-------------------
   (has-type Γ number Int)]

  [-------------------
   (has-type Γ B Bool)]

  [(lookup Γ x τ)
   -------------------
   (has-type Γ x τ)]

  [(has-type (extend Γ (x : τ_1)) e τ_2)
   -------------------
   (has-type Γ (λ (x : τ_1) → e) (τ_1 → τ_2))]

  [(has-type Γ e_1 (τ_1 → τ_2))
   (has-type Γ e_2 τ_1)
   -------------------
   (has-type Γ (e_1 e_2) τ_2)]

   [(has-type Γ ((e_1 e_2) e_3 ...) τ)
    -------------------
    (has-type Γ (e_1 e_2 e_3 ...) τ)]


  [(lookup Γ e D) (lookup Γ L ((L : D >-> layout[x ...]) layout-case))
   -------------------
   (has-type Γ ((lower [y ...] L) e) L)]
)

(define-judgment-form fun-SuSLik
  #:contract (match-pat-con C e)
  #:mode (match-pat-con O I)

  [-------------------
   (match-pat-con C (C))]

  [-------------------
   (match-pat-con C (C e ...))])

(define-judgment-form fun-SuSLik
  #:contract (pat-con-apart C pat)
  #:mode (pat-con-apart I I)

  [(where #t (different C C_2))
   -------------------
   (pat-con-apart C C_2)]

  [(where #t (different C C_2))
   -------------------
   (pat-con-apart C (C_2 x ...))])

(define (zip xs ys)
  (for/list ([x xs]
             [y ys])
    (list x y)))

;;;;;;; Layout application reduction
(define-judgment-form fun-SuSLik
  #:contract (lookup-layout-case C layout-cases layout-case)
  #:mode (lookup-layout-case I I O)

  [(match-pat-con C pat)
   -------------------
   (lookup-layout-case C ([x ...] pat → fs-assertion) ([x ...] pat → fs-assertion))] 

  [(match-pat-con C pat)
   -------------------
   (lookup-layout-case C (([x ...] pat → fs-assertion) layout-cases) ([x ...] pat → fs-assertion))]

  [(lookup-layout-case C layout-cases layout-case)
   (pat-con-apart C pat)
   -------------------
   (lookup-layout-case C (([x ...] pat → fs-assertion) layout-cases) layout-case)])

(define-judgment-form fun-SuSLik
  #:contract (lookup-layout-fn-case C layout-fn-def layout-case [x ...])
  #:mode (lookup-layout-fn-case I I O O)

  [(lookup-layout-case C layout-cases layout-case)
   -------------------
   (lookup-layout-fn-case C ((L : τ >-> layout [x ...]) layout-cases) layout-case [x ...])])

(define-judgment-form fun-SuSLik
  #:contract (lookup-layout-case-in-ctx Γ L C layout-case)
  #:mode (lookup-layout-case-in-ctx I I I O)

  [(lookup Γ L layout-fn-def)
   (lookup-layout-fn-case C layout-fn-def layout-case [x ...])
   -------------------
   (lookup-layout-case-in-ctx Γ L C layout-case)])


(define-judgment-form fun-SuSLik
  #:contract (layout-case-subst layout-case constr-app [e ...] layout-case)
  #:mode (layout-case-subst I I I O)

  [-------------------
   (layout-case-subst ([x ...] (C y ...) → fs-assertion)
                      (C e ...)
                      [z ...]
                      ([x ...] (C y ...) →
                               #;(substitute (substitute fs-assertion [x z] ...) [y e] ...)
                               (substitute (substitute fs-assertion ,@(zip (term (x ...)) (term (z ...)))) [y e] ...)
                               ))])

; Turn (L [x y ...] a) into (x = a).
; This is for use in get-arg-assertion.
(define layout-app->eq
  (reduction-relation
   fun-SuSLik
   #:domain fs-assertion
   #:codomain fs-assertion

   (--> (in-hole fs-assertion-hole (L [x y ...] a))
        (in-hole fs-assertion-hole (x = a)))))

(define fs-assertion->suslik
  (reduction-relation
   fun-SuSLik
   #:domain fs-assertion
   #:codomain suslik-heaplets

   (--> (in-hole fs-assertion-hole (L [x ...] a ...))
        (in-hole fs-assertion-hole (L x ... a ...)))))

; Find the fs-assertion associated to the (pattern) arrgument to a fun-SuSLik function. This will
; be used in the generated SuSLik to effectively "destructure" the "argument" parameter of the
; inductive predicate.
(define-judgment-form fun-SuSLik
  #:contract (get-arg-assertion Γ L [x ...] pat fs-assertion)
  #:mode (get-arg-assertion I I I I O)

  [(lookup-layout-case-in-ctx Γ L C layout-case)
   (layout-case-subst layout-case (C e ...) [x ...] ([y ...] (C z ...) → fs-assertion))
   (where fs-assertion_r ,(car (apply-reduction-relation* layout-app->eq (term fs-assertion))))
   -------------------
   (get-arg-assertion Γ L [x ...] (C e ...) fs-assertion_r)])

; For something related, see https://github.com/roboguy13/suslik/wiki/Ideas-on-predicate-composition#a-syntactic-transformation-for-predicate-composition
; Precondition: Each list of compose-args contains exactly one '?
(define-judgment-form fun-SuSLik
  #:contract (fs-compose Γ L x compose-app L compose-app fs-assertion)
  #:mode (fs-compose I I I I I I O)

  [(where x_shared ,(gensym 'shared))
   (where e_1 (substitute compose-app_1 [? x_shared]))
   ;(where e_2 (substitute compose-app_2 [? x_shared]))
   (where e_2 compose-app_2)
   (lower-expr Γ x e_1 (fs-heaplet_0 ...))
   (where (fs-heaplet_1 ...) ,(car (apply-reduction-relation layout-app->eq (term (fs-heaplet_0 ...)))))
   (lower-expr Γ x_shared e_2 (fs-heaplet_2 ...))
   ;(lower-expr Γ x_0 compose-app
   ;(apply-layout Γ L_1 [x_0 x ...] (substitute [C compose-arg_1 ...] [? x_shared]) (fs-heaplets_1 ...))
   ;(apply-layout Γ L_2 [y_0 y ...] (substitute [
   -------------------
   (fs-compose Γ
               L_1 x compose-app_1
               L_2 compose-app_2
               (fs-heaplet_1 ... fs-heaplet_2 ...))
   ])

(define-judgment-form fun-SuSLik
  #:contract (fs-compose* Γ x compose-app* fs-assertion)
  #:mode (fs-compose* I I I O)

  [(lower-expr Γ x (f y ...) fs-assertion)
   --------------------
   (fs-compose* Γ x (f y ...) fs-assertion)
   ]

  [(lower-expr Γ x (lower [] L (C y ...)) fs-assertion)
   --------------------
   (fs-compose* Γ x (lower [] L (C y ...)) fs-assertion)]

  [(fs-compose* Γ x (g e ...) fs-assertion_1) ; TODO: Figure out how to combine this
   (fs-compose Γ L x (lower [] L (f z ... ?)) L (g e ...) fs-assertion)
   --------------------
   (fs-compose* Γ x (lower [] L (f z ... (g e ...))) fs-assertion)
   ])

; Either apply (expand) a layout application or turn a function application into
; its corresponding layout application form (without expanding it)
(define-judgment-form fun-SuSLik
  #:contract (lower-expr Γ x compose-app fs-assertion)
  #:mode (lower-expr I I I O)

  [(apply-layout Γ L [x] (C e ...) fs-assertion)
   -------------------
   (lower-expr Γ x (lower [] L (C e ...)) fs-assertion)]

  [-------------------
   (lower-expr Γ x (f e ...) (((get-pred-name f) [x] e ...)))])

#;(define-judgment-form fun-SuSLik
  #:contract (layout-case-subst* layout-case constr-app))

(define-judgment-form fun-SuSLik
  #:contract (value? e boolean)
  #:mode (value? I O)

  [--------------------
   (value? (C) #t)]

  [--------------------
   (value? (λ x e) #t)]
  
  [(value? (C x_s ...) boolean_1)
   (value? x boolean_2)
   --------------------
   (value? (C x x_s ...) ,(and (term boolean_1) (term boolean_2)))]

  [--------------------
   (value? boolean #t)]

  [--------------------
   (value? integer #t)])

(define-judgment-form fun-SuSLik
  #:contract (hereditary-base-value? e boolean)
  #:mode (hereditary-base-value? I O)

  [--------------------
   (hereditary-base-value? (C) #t)]

  [--------------------
   (hereditary-base-value? x #t)] ; TODO: Is this correct?
  
  [(hereditary-base-value? (C x_s ...) boolean_1)
   (hereditary-base-value? x boolean_2)
   --------------------
   (hereditary-base-value? (C x x_s ...) ,(and (term boolean_1) (term boolean_2)))]

  [--------------------
   (hereditary-base-value? boolean #t)]

  [--------------------
   (hereditary-base-value? integer #t)])

(define (reduce-layout-apps Γ)
  (reduction-relation
   fun-SuSLik
   #:domain fs-assertion-applied
   
   [--> (in-hole fs-assertion-hole (L [x ...] (C e ...)))
        (in-hole fs-assertion-hole fs-assertion_r)

        #;(judgment-holds (hereditary-base-value? (C e ...) #t))
        (judgment-holds (lookup-layout-case-in-ctx ,Γ L C layout-case))
        (judgment-holds (layout-case-subst layout-case
                                  (C e ...)
                                  [x ...]
                                  ([x_2 ...] (C y_2 ...) → fs-assertion_r)))
        #;(judgment-holds (freshen-given [x ...] fs-assertion_r0 fs-assertion_r))]))

(define flatten-assertion-red
  (reduction-relation
   fun-SuSLik
   #:domain fs-assertion-applied

   [--> (in-hole flatten-assertion-applied (fs-heaplet_0 ... (fs-heaplet ...) fs-heaplet-applied ...))
        (in-hole flatten-assertion-applied (fs-heaplet_0 ... fs-heaplet ... fs-heaplet-applied ...))]))


(define-judgment-form fun-SuSLik
  #:contract (flat-reduce-layout-apps Γ fs-assertion fs-assertion)
  #:mode (flat-reduce-layout-apps I I O)

  ((where fs-assertion-applied ,(car (apply-reduction-relation* (reduce-layout-apps (term Γ)) (term fs-assertion))))
   (where fs-assertion_r ,(car (apply-reduction-relation* flatten-assertion-red (term fs-assertion-applied))))
   ------------------
   (flat-reduce-layout-apps Γ fs-assertion fs-assertion_r)))

(define-judgment-form fun-SuSLik
  #:contract (apply-layout Γ L [a ...] constr-app fs-assertion)
  #:mode (apply-layout I I I I O)

  [(lookup-layout-case-in-ctx Γ L C ([x ...] (C y ...) → fs-assertion_0))
   (layout-case-subst ([x ...] (C y ...) → fs-assertion_0) (C e ...) [a ...] ([b ...] (C y_2 ...) → fs-assertion_r0))
   (flat-reduce-layout-apps Γ fs-assertion_r0 fs-assertion_r)
   #;(hereditary-base-value? (C e ...) #t)
   ------------------
   (apply-layout Γ L [a ...] (C e ...) fs-assertion_r)])

;;;;;;;

(define-judgment-form fun-SuSLik
  #:contract (nonzero-vars fs-assertion [x ...])
  #:mode (nonzero-vars I O)

  [------------------
   (nonzero-vars () [])]

  [(nonzero-vars (fs-heaplet ...) [x ...])
   ------------------
   (nonzero-vars (emp fs-heaplet ...) [x ...])]

  [(nonzero-vars (fs-heaplet ...) [x ...])
   ------------------
   (nonzero-vars ((y :-> pointed-to) fs-heaplet ...) [y x ...])
   ]

  [(nonzero-vars (fs-heaplet ...) [x ...])
   ------------------
   (nonzero-vars (((y + n) :-> pointed-to) fs-heaplet ...) [y x ...])
   ]

  [(nonzero-vars (fs-heaplet ...) [x ...])
   ------------------
   (nonzero-vars ((y = 0) fs-heaplet ...) [x ...])]

  [(nonzero-vars (fs-heaplet ...) [x ...])
   ------------------
   (nonzero-vars (layout-app fs-heaplet ...) [x ...])]
  )


(define-judgment-form fun-SuSLik
  #:contract (case-condition Γ L [x ...] pat e)
  #:mode (case-condition I I I I O)

  ; TODO: Change this to check based on heap satisfaction?
  [(apply-layout Γ L [x ...] pat fs-assertion_0)
   (nonzero-vars fs-assertion_0 [x_nonzero-initial ...])
   (where [x_nonzero ...] ,(remove-duplicates (term [x_nonzero-initial ...])))
   (where [x_zero ...] ,(remove* (term [x_nonzero ...]) (term [x ...])))
   (where [e_zero-cond ...] ,(map (λ (v) (term (== ,v 0))) (term [x_zero ...])))
   (where [e_nonzero-cond ...] ,(map (λ (v) (term (not (== ,v 0)))) (term [x_nonzero ...])))
   ------------------
   (case-condition Γ L [x ...] pat
                   (&& e_nonzero-cond ... e_zero-cond ...)
                   #;,(foldr (λ (arg acc) (term (&& ,arg ,acc))) (term true) (append (term [e_nonzero-cond ...]) (term [e_zero-cond ...]))))])

(define-judgment-form fun-SuSLik
  #:contract (subst-layout-name L L_2 fs-assertion fs-assertion)
  #:mode (subst-layout-name I I I O)

  [-----------------
   (subst-layout-name L L_2 fs-assertion (substitute fs-assertion (L L_2)))])

(define-metafunction fun-SuSLik
  get-pred-name : x -> y
  ((get-pred-name x)
   ,(string->symbol (string-append "L-pred_base_" (symbol->string (term x))))))

(define-metafunction fun-SuSLik
  get-inner-pred-name : x -> y
  ((get-inner-pred-name x)
   ,(string->symbol (string-append "L-pred_inner_" (symbol->string (term x))))))

; (L (x ...) e) ... --> (L x ...)
(define to-suslik-layout-apps
  (reduction-relation
   fun-SuSLik
   #:domain fs-assertion-applied
   #:codomain (suslik-heaplet ...)
   
   [--> (in-hole fs-assertion-hole (L [x ...] e ...))
        (in-hole fs-assertion-hole (L x ...))]))


#;(define (lower->suslik-layout-app Γ)
  (reduction-relation
   fun-SuSLik
   #:domain e
   #:codomain (suslik-heaplet ...)
   
   [--> (in-hole fs-assertion-hole (lower [x ...] L pat))
        (in-hole fs-assertion-hole fs-assertion)

        (judgment-holds (flat-reduce-layout-apps Γ (L [x ...] pat) fs-assertion))]))

(define-judgment-form fun-SuSLik
  #:contract (lower->suslik-layout-app Γ e fs-assertion)
  #:mode (lower->suslik-layout-app I I O)

  [(flat-reduce-layout-apps Γ ((L [x ...] pat)) fs-assertion)
   ---------------
   (lower->suslik-layout-app Γ (lower [x ...] L pat) fs-assertion)])

(define (to-and xs)
  (let ((len (length xs)))
    (if (eq? len 0)
        (term true)
        (if (eq? len 1)
            (car xs)
            (term (&& ,@xs))))))



(define-judgment-form fun-SuSLik
  #:contract (gen-cond-branch Γ L [x ...] pat guarded-expr pred-branch)
  #:mode (gen-cond-branch I I I I I O)

  [(apply-layout Γ L [x ...] pat fs-assertion)
   (where (suslik-heaplet ...) ,(car (apply-reduction-relation* to-suslik-layout-apps (term fs-assertion))))
   (where (suslik-heaplet_e ...) ,(car (apply-reduction-relation* lower->suslik-layout-app (term e))))
   -----------------
   (gen-cond-branch Γ L [x ...] pat (bool-expr → e) (bool-expr ⇒ (true (suslik-heaplet ... suslik-heaplet_e ...))) #;(true fs-assertion) #;(true (substitute fs-assertion [L (get-pred-name f)])))
   ]

  #;[(apply-layout Γ L [x ...] pat fs-assertion)
   -----------------
   (gen-match-branch Γ L [x ...] f (pat [bool-expr_0 bool-expr ...] → e) (substitute fs-assertion [L (get-inner-pred-name f)]))])

(define-judgment-form fun-SuSLik
  #:contract (gen-cond-branch* Γ L [x ...] pat (guarded-expr ...) (pred-branch ...))
  #:mode (gen-cond-branch* I I I I I O)

  [----------------
   (gen-cond-branch* Γ L [x ...] pat [] [])
   ]

  [(gen-cond-branch Γ L [x ...] pat (bool-expr → e) pred-branch)
   (gen-cond-branch* Γ L [x ...] pat (guarded-expr ...) (pred-branch_r ...))
   ----------------
   (gen-cond-branch* Γ L [x ...] pat ((bool-expr → e) guarded-expr ...) (pred-branch pred-branch_r ...))
   ])

(define-judgment-form fun-SuSLik
  #:contract (gen-cond-branch-inductive Γ L [x ...] pred-name (pat guarded-expr ...) suslik-predicate)
  #:mode (gen-cond-branch-inductive I I I I I O)

  [(gen-cond-branch* Γ L [x ...] pat (guarded-expr ...) (pred-branch ...))
   ------------------
   (gen-cond-branch-inductive Γ L [x ...] pred-name (pat guarded-expr ...)
                               (inductive pred-name [x ...] pred-branch ...))
   ])


(define-judgment-form fun-SuSLik
  #:contract (get-result-arg layout-app x)
  #:mode (get-result-arg I O)

  [----------------
   (get-result-arg (L [z x ...] e) z)])

(define-judgment-form fun-SuSLik
  #:contract (add-result-arg layout-app x layout-app)
  #:mode (add-result-arg I I O)

  [------------------
   (add-result-arg (L [x ...] e) z (L [z x ...] e))])

(define (add-result-arg-red L r)
  (reduction-relation
   fun-SuSLik
   #:domain fs-assertion
   #:codomain fs-assertion

   (--> (in-hole fs-assertion-hole (L [x ...] e))
        (in-hole fs-assertion-hole (L [r x ...] e))
        (where #t ,(eq? L (term L)))
        
        #;(judgment-holds (add-result-arg (L [x ...] e) r fs-assertion)))))

(define-judgment-form fun-SuSLik
  #:contract (gen-match-branch Γ L [x ...] pred-name pat guarded-expr pred-branch)
  #:mode (gen-match-branch I I I I I I O)

  [(case-condition Γ L [x y ...] pat e_cond)
   (where x_pat ,(gensym (term arg)))
   (apply-layout Γ L [x_pat] pat fs-assertion_pat)
   ;(where L_new ,(gensym (term L)))
   (fs-compose* Γ x e fs-assertion_1)
   (where (suslik-heaplet_1 ...) ,(car (apply-reduction-relation* fs-assertion->suslik (term fs-assertion_1))))
   (where (suslik-heaplet_pat ...) ,(car (apply-reduction-relation* fs-assertion->suslik (term fs-assertion_pat))))
   #;(where fs-assertion_2 ,(car (apply-reduction-relation (add-result-arg-red (term L) (term x_res)) (term fs-assertion_1))))
   -------------------
   (gen-match-branch Γ L [x y ...] pred-name pat (true → e)
                     (e_cond ⇒ (true (suslik-heaplet_pat ... suslik-heaplet_1 ...) #;(substitute fs-assertion_1 (L L_new)))))
   ])

(define-judgment-form fun-SuSLik
  #:contract (gen-match-branch* Γ L [x ...] pred-name (fn-case ...) (pred-branch ...))
  #:mode (gen-match-branch* I I I I I O)

  [--------------------
   (gen-match-branch* Γ L [x ...] pred-name [] [])]

  [(gen-match-branch Γ L [x ...] pred-name pat guarded-expr pred-branch)
   (gen-match-branch* Γ L [x ...] pred-name (fn-case ...) (pred-branch_r ...))
   --------------------
   (gen-match-branch* Γ L [x ...] pred-name
                      ((pat guarded-expr) fn-case ...)
                      (pred-branch pred-branch_r ...))])

#;(define filter-lt-7
  (term
   ((filterLt7 : (List → List))
    (
     ((C-Nil) [true → (C-Nil)])
     ((C-Cons head tail)
      [(< a 7) → (C-Cons head (filterLt7 tail))]
      [(not (< a 7)) → (filterLt7 tail)])))))

(define-judgment-form fun-SuSLik
  #:contract (gen-match-pred Γ L [x ...] pred-name fn-def suslik-predicate)
  #:mode (gen-match-pred I I I I I O)

  [#;(where z ,(gensym 'arg))
   (gen-match-branch* Γ L [x ...] pred-name (fn-case ...) (pred-branch ...))
   -------------------
   (gen-match-pred Γ L [x ...] pred-name
                   ((f : τ)
                    (fn-case ...))
                   (inductive pred-name [x ...] pred-branch ...))])

;(define-judgment-form fun-SuSLik

#;(define-judgment-form fun-SuSLik
  #:contract (gen-match-predicate Γ L [x ...] fn-def predicate)
  #:mode (gen-match-predicate I I I I O)

  [#;(gen-guard-predicate Γ )
   (apply-layout Γ L [x ...])
   ------------------
   (gen-match-predicate Γ L [x ...]
                        ((f : τ)
                         ((pat guard → e) ...))
                        predicate)]
   )


;;;;;;; Transformations in the functional language

#;(define (push-lower-inward Γ)
  (reduction-relation
   fun-SuSLik

   #;[--> (in-hole e-lower (f (C e ...)))
        (in-hole e-lower (f ,@(map (λ(arg) (term (lower L ,arg))) (term (e ...)))))]

   [--> (in-hole e-lower (lower L (f (lift L e) ...)))
        ]))


(define (lower-case-lift Γ)
  (reduction-relation
   fun-SuSLik

   [--> (in-hole instantiate-e (lower [x ...] L_1 (match (lift [y ...] L_2 e) match-cases)))
        (in-hole instantiate-e (lower [x ...] L_1 (match (lift [y ...] L_2 e) match-cases)))]))


;;;;;;;



(define (defs ds)
  (if (null? ds)
      (term ·)
      (term (extend ,(defs (cdr ds)) ,(first (car ds)) ,(second (car ds))))))

(define List-ty (defs `[,(term (Nil : List)) ,(term (Cons : (Int → (List → List))))]))

(define D-layout
  (term
   ((L-D : D >-> layout [x])
    (
     ([x] (C-D1 a) → ((x :-> a)))
     ([x] (C-D2 a b) → ((x :-> a) ((x + 1) :-> b)))))))

(define D-ctx (term (extend · L-D ,D-layout)))

(define sll-layout
  (term
   ((L-sll : List >-> layout [x])
    (
     ([x] (C-Nil) → ((x = 0)))
     ([x nxt] (C-Cons head tail) →
       ((x :-> head)
        ((x + 1) :-> nxt)
        (L-sll [nxt] tail)))))))

(define sll-ctx (term (extend · L-sll ,sll-layout)))

(define dll-layout
  (term
   ((L-dll : List >-> layout [x z])
    (
     ([x z] (C-Nil) → ((x = 0) (z = 0)))
     ([x z w] (C-Cons head tail) →
              ((x :-> head)
               ((x + 1) :-> w)
               ((x + 2) :-> z)
               (L-dll [w x] tail)))))))

(define dll-ctx (term (extend · L-dll ,dll-layout)))

(define filter-lt-7
  (term
   ((filterLt7 : (List → List))
    (
     ((C-Nil) [true → (C-Nil)])
     ((C-Cons head tail)
      [(< a 7) → (C-Cons head (filterLt7 tail))]
      [(not (< a 7)) → (filterLt7 tail)])))))


(define D-to-list
  (term
   ((DToList : (D → List))
    (
    ((C-D1 a) [true → (C-Cons a (C-Nil))])
    ((C-D2 a b) [true → (C-Cons a (C-Cons b (C-Nil)))])))))

(define D-to-list-sll
  (term
   ((DToList : (D → List))
    (
    ((C-D1 a) [true → (lower [] L-sll (C-Cons a (C-Nil)))])
    #;((C-D2 a b) [true → (lower [] L-sll (C-Cons a (C-Cons b (C-Nil))))])))))

(define tree-layout
  (term
   ((L-tree : Tree >-> layout [x])
    (
     ([x] (C-Leaf) → ((x = 0)))
     ([x nxtLeft nxtRight] (C-Bin item left right) →
          ((x :-> item)
           ((x + 1) :-> nxtLeft)
           ((x + 2) :-> nxtRight)
           (L-tree [nxtLeft] left)
           (L-tree [nxtRight] right)))))))

(define compose-test
  (term
   ((f : (List → List))
    [
     [(C-Nil) (true → (lower [] L-sll (C-Nil)))]
     [(C-Cons a b) (true → (lower [] L-sll (C-Cons a (f b))))]])
   ))

(define left-list
  (term
   ((left-list : (Tree → List))
    (
     [(C-Leaf) (true → (lower [] L-sll (C-Nil)))]
     [(C-Bin a left right) (true → (lower [] L-sll (C-Cons a (left-list left))))]
     ))))

(define tree-ctx (term (extend · L-tree ,tree-layout)))

(define all-ctx (defs `((,(term L-tree) ,tree-layout)
                        (,(term L-sll) ,sll-layout)
                        (,(term L-D) ,D-layout))))

#;(current-traced-metafunctions '(reduce-layout-inst))
#;(current-traced-metafunctions '(layout-pat-match))

#;(current-traced-metafunctions '(apply-layout-case reduce-layout-case))
#;(current-traced-metafunctions '(layout-case-subst))
#;(current-traced-metafunctions '(apply-layout-case reduce-layout-case))

#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b c)) fs-assertion) fs-assertion)



(judgment-holds (apply-layout ,sll-ctx L-sll [x] (C-Nil) fs-assertion) fs-assertion)

(judgment-holds (apply-layout ,dll-ctx L-dll [x z] (C-Nil) fs-assertion) fs-assertion)

(judgment-holds (apply-layout ,sll-ctx L-sll [x] (C-Cons 1 (C-Cons 2 (C-Cons 3 (C-Nil)))) fs-assertion) fs-assertion)

(judgment-holds (apply-layout ,sll-ctx L-sll [x] (C-Cons a (C-Cons b (C-Cons c (C-Nil)))) fs-assertion) fs-assertion)

(judgment-holds (apply-layout ,dll-ctx L-dll [x z] (C-Cons 4 (C-Cons 5 (C-Cons 6 e))) fs-assertion) fs-assertion)


(judgment-holds (apply-layout ,tree-ctx L-tree [x] (C-Bin 1 (C-Leaf) (C-Leaf)) fs-assertion) fs-assertion)
(judgment-holds (apply-layout ,tree-ctx L-tree [x] (C-Bin 1 (C-Bin 2 a b) (C-Bin 3 c (C-Leaf))) fs-assertion) fs-assertion)
(redex-match fun-SuSLik fn-def filter-lt-7)
(judgment-holds (apply-layout ,sll-ctx L-sll [x] (C-Cons a b) fs-assertion) fs-assertion)
(judgment-holds (apply-layout ,dll-ctx L-dll [x] (C-Cons a b) fs-assertion) fs-assertion)

(judgment-holds (gen-match-pred ,all-ctx L-tree [x] L-pred-f ,left-list any) any)


#;(inductive
    L-pred-f
    (x)
    ((&& (== x 0)) ⇒ (true ((x = 0) (x = 0))))
    ((&& (not (== x 0)))
     ⇒
     (true
      ((x :-> a)
       ((x + 1) :-> nxtLeft«391»)
       ((x + 2) :-> nxtRight«392»)
       (L-tree (nxtLeft«391») left)
       (L-tree nxtRight«392» right)
       (x :-> a)
       ((x + 1) :-> nxt«407»)
       (nxt«407» = shared954743)
       (L-pred_base_left-list shared954743 left)))))









#;
((inductive L-pred-f (x)
            ((&& (== x 0)) ⇒ (true ((x = 0))))
            ((&& (not (== x 0))) ⇒
                                 (true
                                  ((x :-> a)
                                   ((x + 1) :-> nxt«382»)
                                   (nxt«382» = shared752366)
                                   (L-pred_base_left-list shared752366 left))))))



#;(judgment-holds (apply-layout ,sll-ctx sll (C-Cons a (C-Cons b (C-Cons (+ 1 1) (C-Nil)))) fs-assertion) fs-assertion)




#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b (Nil))) fs-assertion) fs-assertion)


#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (C-Cons a (C-Cons b (C-Cons c d))) fs-assertion) fs-assertion)

#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a b) fs-assertion) fs-assertion)

#;(judgment-holds (layout-inst-fn ,dll-ctx [x z] ,dll-layout (Cons a (Cons b (Nil))) fs-assertion) fs-assertion)
