#lang racket

(require redex)
(require racket/set)

(define-language fun-SuSLik
  (data-def ::= (data D where alt ...))
  (alt ::= (C τ ...))
  (τ ::= Int Bool (τ → τ) D)
  (Γ ::= · (extend Γ (x : τ)) (extend Γ L layout-fn-def))
  ;(Σ ::= · (extend Σ layout-fn-def))
  (fn-def ::= ((f : τ) fn-cases))
  (fn-case ::= (pat → e))
  (fn-cases ::= fn-case (fn-case fn-cases))
  (layout-fn-def ::= ((L : τ >-> layout [ x ... ]) layout-cases))
  (layout-case ::= ([x ...] pat → fs-assertion))
  (layout-cases ::= layout-case (layout-case layout-cases))
  (fs-heaplet κ ::= emp (p :-> y) (p = 0) (L [x ...] layout-arg))
  (fs-assertion ::= (fs-heaplet ...))
  (layout-arg ::= y constr-app)
  (pat ::= C (C x ...))
  (p ::= x (x + n))
  (n ::= natural)
  (I ::= integer)
  (B ::= boolean)
  (base-val ::= integer boolean x)
  (params ::= [x ...])
  (constr-app ::= C (C e ...))
  (e ::= x I B (e_1 e_2 ...) (λ (a : τ) → e) (let x := e_1 in e_2) (e_1 e_2) builtin)
  (builtin ::= ite le eq add sub and or not (lower L))
  (D L a b f g h x y z i j k ::= variable-not-otherwise-mentioned)
  (C ::= (variable-prefix C-))

  (fs-heaplet-applied ::= fs-heaplet (fs-heaplet-applied ...))
  (fs-assertion-applied ::= (fs-heaplet-applied ...))

  (layout-case-hole ::= ([x ...] pat → fs-assertion-hole))
  (fs-assertion-hole ::= hole (fs-assertion-hole fs-heaplet ...) (fs-heaplet ... fs-assertion-hole))

  (flatten-assertion-applied ::= hole (flatten-assertion-applied fs-heaplet-applied ...) (fs-heaplet ... flatten-assertion-applied))
  #:binding-forms
  (λ (x : τ) → e #:refers-to x)
  (let x := e_1 in e_2 #:refers-to x)
  (((f_1 : τ) ((C x ...) := e #:refers-to (shadow x ...)) ...))
  ([x ...] (C y ...) → fs-assertion #:refers-to (shadow x ... y ...)))

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
  #:contract (get-assertion-vars fs-assertion [x ...])
  #:mode (get-assertion-vars I O)

  [-----------------
   (get-assertion-vars (x :-> y) [x y])]

  [-----------------
   (get-assertion-vars ((x + n) :-> y) [x y])]

  [-----------------
   (get-assertion-vars (x = 0) [x])]

  [-----------------
   (get-assertion-vars (L [x ...] layout-arg) [x ...])])

(define-judgment-form fun-SuSLik
  #:contract (get-layout-case-vars layout-case [x ...])
  #:mode (get-layout-case-vars I O)

  [(get-assertion-vars fs-assertion [x ...])
   ------------------
   (get-layout-case-vars ([y ...] (C z ...) → fs-assertion) [x ... y ...])])

(define-judgment-form fun-SuSLik
  #:contract (get-layout-case-heap-vars layout-case [x ...])
  #:mode (get-layout-case-heap-vars I O)

  [(get-layout-case-vars ([y ...] (C z ...) → fs-assertion) [a ...])
   ------------------
   (get-layout-case-heap-vars ([y ...] (C z ...) → fs-assertion) ,(set->list (set-subtract (list->set (term [a ...])) (list->set (term [z ...])))))]
  )

(define (zip xs ys)
  (for/list ([x xs]
             [y ys])
    (list x y)))

(define-judgment-form fun-SuSLik
  #:contract (layout-case-subst layout-case constr-app [z ...] layout-case)
  #:mode (layout-case-subst I I I O)

  [-------------------
   (layout-case-subst ([x ...] (C y ...) → fs-assertion)
                      (C e ...)
                      [z ...]
                      ([x ...] (C y ...) →
                               #;(substitute (substitute fs-assertion [x z] ...) [y e] ...)
                               (substitute (substitute fs-assertion ,@(zip (term (x ...)) (term (z ...)))) [y e] ...)
                               ))])

(define-judgment-form fun-SuSLik
  #:contract (freshen-given [x ...] fs-assertion fs-assertion)
  #:mode (freshen-given I I O)

  [-------------------
   (freshen-given [x ...] fs-assertion (substitute fs-assertion ,@(map (λ(arg) (list arg (gensym arg))) (term (x ...)))))])

(define (reduce-layout-apps Γ)
  (reduction-relation
   fun-SuSLik
   ; #:domain fs-assertion-applied
   
   [--> (in-hole fs-assertion-hole (L [x ...] (C e ...)))
        (in-hole fs-assertion-hole fs-assertion_r)

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

   [--> (in-hole flatten-assertion-applied (fs-heaplet_0 ... (fs-heaplet ...)))
        (in-hole flatten-assertion-applied (fs-heaplet_0 ... fs-heaplet ...))]))


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
   ------------------
   (apply-layout Γ L (C e ...) fs-assertion_r)])


(define (defs ds)
  (if (null? ds)
      (term ·)
      (term (extend ,(defs (cdr ds)) ,(car ds)))))

(define List-ty (defs `[,(term (Nil : List)) ,(term (Cons : (Int → (List → List))))]))

(define sll-layout
  (term
   ((sll : List >-> layout [x])
    (
     ([x] (C-Nil) → ((x = 0)))
     ([x nxt] (C-Cons head tail) →
       ((x :-> head) ((x + 1) :-> nxt) (sll [nxt] tail)))))))

(define sll-ctx (term (extend · sll ,sll-layout)))

(define dll-layout
  (term
   ((dll : List >-> layout [x z])
    (
     ([x z] (C-Nil) → ((x = 0)))
     ([x z] (C-Cons head tail) →
                       ((x :-> head) ((x + 1) :-> w)
                                     ((x + 2) :-> z)
                                     (dll [w x] tail)))))))

(define dll-ctx (term (extend · dll ,dll-layout)))


#;(current-traced-metafunctions '(reduce-layout-inst))
#;(current-traced-metafunctions '(layout-pat-match))

#;(current-traced-metafunctions '(apply-layout-case reduce-layout-case))
#;(current-traced-metafunctions '(layout-case-subst))
#;(current-traced-metafunctions '(apply-layout-case reduce-layout-case))

#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b c)) fs-assertion) fs-assertion)


(judgment-holds (apply-layout ,sll-ctx sll (C-Cons a (C-Cons b (C-Cons c (C-Nil)))) fs-assertion) fs-assertion)

#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b (Nil))) fs-assertion) fs-assertion)


#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (C-Cons a (C-Cons b (C-Cons c d))) fs-assertion) fs-assertion)

#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a b) fs-assertion) fs-assertion)

#;(judgment-holds (layout-inst-fn ,dll-ctx [x z] ,dll-layout (Cons a (Cons b (Nil))) fs-assertion) fs-assertion)
