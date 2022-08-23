#lang racket

(require redex)
(require racket/set)

(define-language fun-SuSLik
  (data-def ::= (data D where alt ...))
  (alt ::= (C τ ...))
  (τ ::= Int Bool (τ → τ) D)
  (Γ ::= · (extend Γ (x : τ)) (extend Γ L layout-fn-def))
  ;(Σ ::= · (extend Σ layout-fn-def))
  (fn-def ::= ((f : τ) ((pat → e) ...)))
  (match-expr ::= (match e match-cases))
  (match-case ::= (pat → e))
  (match-cases ::= match-case (match-case match-cases))
  (layout-fn-def ::= ((L : τ >-> layout [ x ... ]) layout-cases))
  (layout-case ::= ([x ...] pat → fs-assertion))
  (layout-cases ::= layout-case (layout-case layout-cases))
  (fs-heaplet κ ::= emp (p :-> pointed-to) (p = 0) layout-app)
  (fs-heaplet-val ::= emp (p :-> pointed-to) (p = 0) (L [x ...] pointed-to))
  (layout-app ::= (L [x ...] layout-arg))
  (fs-assertion ::= (fs-heaplet ...))
  (layout-arg ::= y constr-app (lower L e))
  (pat ::= C (C x ...))
  (p ::= x (x + n))
  (n ::= natural)
  (I ::= integer)
  (B ::= boolean)
  (pointed-to ::= base-val x)
  (base-val ::= integer boolean)
  (params ::= [x ...])
  (constr-app ::= C (C e ...))
  (e ::= x I B match-expr (e_1 e_2 ...) (λ (a : τ) → e) (let x := e_1 in e_2) (e_1 e_2) builtin)
  (builtin ::= ite <= == + - && || not (lower L e) (lift L e))
  (D L a b f g h x y z i j k ::= variable-not-otherwise-mentioned)
  (C ::= (variable-prefix C-))

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

  (lowered ::= value (lower L value))
  (lifted ::= value (lift L value))
  (instantiate-e ::= hole
           (instantiate-e e ...)
           (lower L instantiate-e)
           #;(C lowered ... e-lower e ...)
           (lower L (f lifted ... instantiate-e e ...))
           #;(lower L (match lifted match-cases)))

  (suslik-predicate ::=
                    (inductive f (y ...) (pred-branch ...)))
  (pred-branch ::= ((pure-part) ⇒ suslik-assertion))
  (suslik-heaplet ::= emp (p :-> pointed-to) (func f x ...) (L x ...))
  (suslik-assertion ::= (pure-part (suslik-heaplet ...)))
  (pure-part ::= bool-expr)
  (int-expr ::=
            x
            integer
            (int-expr + int-expr)
            (int-expr - int-expr)
            (int-expr * int-expr))
  (bool-expr ::=
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
  (((f_1 : τ) (f x ... := e #:refers-to (shadow x ...)) ...))
  ([x ...] (C y ...) → fs-assertion #:refers-to (shadow x ... y ...))
  (inductive f (y ...) (pred-branch ...) #:refers-to (shadow y ...)))

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
   (where #t (different L M))
   ------------------
   (lookup (extend Γ M Ld2) L layout-fn-def)
   ])


(define-judgment-form fun-SuSLik
  #:contract (has-type Γ e τ)
  #:mode (has-type I I O)
  [-------------------
   (has-type Γ number Int)]

  [-------------------
   (has-type Γ boolean Bool)]

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
   (has-type Γ ((lower L) e) L)]
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
  #:contract (apply-layout Γ L constr-app fs-assertion)
  #:mode (apply-layout I I I O)

  [(lookup-layout-case-in-ctx Γ L C ([x ...] (C y ...) → fs-assertion_0))
   (layout-case-subst ([x ...] (C y ...) → fs-assertion_0) (C e ...) [x ...] ([x_2 ...] (C y_2 ...) → fs-assertion_r0))
   (flat-reduce-layout-apps Γ fs-assertion_r0 fs-assertion_r)
   #;(hereditary-base-value? (C e ...) #t)
   ------------------
   (apply-layout Γ L (C e ...) fs-assertion_r)])

;;;;;;;


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

   [--> (in-hole instantiate-e (lower L_1 (match (lift L_2 e) match-cases)))
        (in-hole instantiate-e (lower L_1 (match (lift L_2 e) match-cases)))]))


;;;;;;;



(define (defs ds)
  (if (null? ds)
      (term ·)
      (term (extend ,(defs (cdr ds)) ,(car ds)))))

(define List-ty (defs `[,(term (Nil : List)) ,(term (Cons : (Int → (List → List))))]))

(define D-layout
  (term
   ((DL : D >-> layout [x])
    (
     ([x] (C-D1 a) → ((x :-> a)))
     ([x] (C-D2 a b) → ((x :-> a) ((x + 1) :-> b)))))))

(define D-ctx (term (extend · DL ,D-layout)))

(define sll-layout
  (term
   ((sll : List >-> layout [x])
    (
     ([x] (C-Nil) → ((x = 0)))
     ([x nxt] (C-Cons head tail) →
       ((x :-> head)
        ((x + 1) :-> nxt)
        (sll [nxt] tail)))))))

(define sll-ctx (term (extend · sll ,sll-layout)))

(define dll-layout
  (term
   ((dll : List >-> layout [x z])
    (
     ([x z] (C-Nil) → ((x = 0)))
     ([x z w] (C-Cons head tail) →
              ((x :-> head)
               ((x + 1) :-> w)
               ((x + 2) :-> z)
               (dll [w x] tail)))))))

(define dll-ctx (term (extend · dll ,dll-layout)))


(define D-to-list
  (term
   ((DToList : (D → List))
    (
    ((C-D1 a) → (C-Cons a (C-Nil)))
    ((C-D2 a b) → (C-Cons a (C-Cons b (C-Nil))))))))

(define tree-layout
  (term
   ((tree : Tree >-> layout [x])
    (
     ([x] (C-Leaf) → ((x = 0)))
     ([x nxtLeft nxtRight] (C-Bin item left right) →
          ((x :-> item)
           ((x + 1) :-> nxtLeft)
           ((x + 2) :-> nxtRight)
           (tree [nxtLeft] left)
           (tree [nxtRight] right)))))))

(define tree-ctx (term (extend · tree ,tree-layout)))

#;(current-traced-metafunctions '(reduce-layout-inst))
#;(current-traced-metafunctions '(layout-pat-match))

#;(current-traced-metafunctions '(apply-layout-case reduce-layout-case))
#;(current-traced-metafunctions '(layout-case-subst))
#;(current-traced-metafunctions '(apply-layout-case reduce-layout-case))

#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b c)) fs-assertion) fs-assertion)




(judgment-holds (apply-layout ,sll-ctx sll (C-Cons 1 (C-Cons 2 (C-Cons 3 (C-Nil)))) fs-assertion) fs-assertion)

(judgment-holds (apply-layout ,sll-ctx sll (C-Cons a (C-Cons b (C-Cons c (C-Nil)))) fs-assertion) fs-assertion)

(judgment-holds (apply-layout ,dll-ctx dll (C-Cons 4 (C-Cons 5 (C-Cons 6 e))) fs-assertion) fs-assertion)

#;(judgment-holds (layout-case-subst ([x nxtLeft nxtRight] (C-Bin item left right) →
          ((x :-> item)
           ((x + 1) :-> nxtLeft)
           ((x + 2) :-> nxtRight)
           (tree [nxtLeft] left)
           (tree [nxtRight] right))) (C-Bin 1 (C-Leaf) (C-Leaf)) [x nxtLeft nxtRight] layout-case) layout-case)


(judgment-holds (apply-layout ,tree-ctx tree (C-Bin 1 (C-Leaf) (C-Leaf)) fs-assertion) fs-assertion)



#;(judgment-holds (apply-layout ,sll-ctx sll (C-Cons a (C-Cons b (C-Cons (+ 1 1) (C-Nil)))) fs-assertion) fs-assertion)




#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b (Nil))) fs-assertion) fs-assertion)


#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (C-Cons a (C-Cons b (C-Cons c d))) fs-assertion) fs-assertion)

#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a b) fs-assertion) fs-assertion)

#;(judgment-holds (layout-inst-fn ,dll-ctx [x z] ,dll-layout (Cons a (Cons b (Nil))) fs-assertion) fs-assertion)
