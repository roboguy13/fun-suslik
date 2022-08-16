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
  (layout-case ::= (pat → fs-assertion))
  (layout-cases ::= layout-case (layout-case layout-cases))
  (fs-heaplet κ ::= emp (p :-> y) (p = 0) (L [x ...] layout-arg))
  (fs-assertion ::= (fs-heaplet ...))
  (layout-arg ::= y constr-app)
  (pat ::= C (C x ...))
  (p ::= x (x + n))
  (n ::= natural)
  (I ::= integer)
  (B ::= boolean)
  (params ::= [x ...])
  (constr-app ::= C (C e ...))
  (e ::= x I B (e_1 e_2 ...) (λ (a : τ) → e) (let x := e_1 in e_2) (e_1 e_2) builtin)
  (builtin ::= ite le eq add sub and or not (lower L))
  (D L C a b f g h x y z i j k ::= variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x : τ) → e #:refers-to x)
  (let x := e_1 in e_2 #:refers-to x)
  (fn-def ((f_1 : τ) ((C x ...) := e #:refers-to (shadow x ...)) ...))
  (layout-case (C y ...) → fs-assertion #:refers-to (shadow y ...))
  (layout-fn-def ((L : τ >-> layout [ x ... ]) layout-cases #:refers-to (shadow x ...))))

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
   (lookup (extend Γ L layout-fn-def) L (layout-freshen-free-vars layout-fn-def))]

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
   (match-pat-con C C)]

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
   (lookup-layout-case C (pat → fs-assertion) (pat → fs-assertion))] 

  [(match-pat-con C pat)
   -------------------
   (lookup-layout-case C ((pat → fs-assertion) layout-cases) (pat → fs-assertion))]

  [(lookup-layout-case C layout-cases layout-case)
   (pat-con-apart C pat)
   -------------------
   (lookup-layout-case C ((pat → fs-assertion) layout-cases) layout-case)])

(define-judgment-form fun-SuSLik
  #:contract (lookup-layout-fn-case C layout-fn-def layout-case [x ...])
  #:mode (lookup-layout-fn-case I I O O)

  [(lookup-layout-case C layout-cases layout-case)
   -------------------
   (lookup-layout-fn-case C ((L : τ >-> layout [x ...]) layout-cases) layout-case [x ...])])

#;(define (substitute-lists e xs ys)
  (substitute e (zip xs ys)))

(define-metafunction fun-SuSLik
  substitute-lists : (fs-assertion [x ...] [y ...]) -> fs-assertion
  [(substitute-lists fs-assertion [x ...] [y ...])
   (substitute-lists fs-assertion (x y) ...)])

#;(define-metafunction fun-SuSLik
  freshen : x -> y
  [(freshen x)
   ,(gensym (term x))])

(define-judgment-form fun-SuSLik
  #:contract (get-pat-vars pat [x ...])
  #:mode (get-pat-vars I O)

  [
   -------------------
   (get-pat-vars C [])]

  [-------------------
   (get-pat-vars (C x ...) [x ...])])

(define-judgment-form fun-SuSLik
  #:contract (pat-match-asn e pat fs-assertion fs-assertion)
  #:mode (pat-match-asn I I I O)

  [-------------------
   (pat-match-asn C C fs-assertion fs-assertion)]

  [-------------------
   (pat-match-asn (C layout-arg) (C x) fs-assertion (substitute fs-assertion (x layout-arg)))]
  
  [(pat-match-asn (C layout-arg_1 ...) (C y ...) (substitute fs-assertion_1 (x layout-arg)) fs-assertion_r)
   -------------------
   (pat-match-asn (C layout-arg layout-arg_1 ...) (C x y ...) fs-assertion_1 fs-assertion_r)])

(define-judgment-form fun-SuSLik
  #:contract (layout-pat-match [x ...] layout-case e [y ...] fs-assertion)
  #:mode (layout-pat-match I I I I O)

  [(pat-match-asn e_arg pat fs-assertion fs-assertion_Applied)
   -------------------
   (layout-pat-match [x ...] (pat → fs-assertion) e_arg [y ...]
                     (substitute fs-assertion_Applied [x y] ...))
   ])

; Freshen variable when it's *not* in the given list
#;(define-judgment-form fun-SuSLik
  #:contract (freshen-var [x ...] y z)
  #:mode (freshen-var I I O)

  [(where #f ,(member (term y) (term [x ...])))
   -------------------
   (freshen-var [x ...] y ,(gensym (term y)))]

  [(where #f ,(eq? #f (member (term y) (term [x ...]))))
   -------------------
   (freshen-var [x ...] y y)]
  )

#;(define-judgment-form fun-SuSLik
  #:contract (p-freshen [x ...] p p_2)
  #:mode (p-freshen I I O)

  [(freshen-var [x ...] y y_2)
   -------------------
   (p-freshen [x ...] y y_2)]

  [(freshen-var [x ...] y y_2)
   -------------------
   (p-freshen [x ...] (y + n) (y_2 + n))])

(define-metafunction fun-SuSLik
  p-var : p -> y
  [(p-var x) x]
  [(p-var (x + n)) x])

(define-metafunction fun-SuSLik
  assertion-vars : fs-assertion -> [x ...]
  [(assertion-vars ()) ()]
  [(assertion-vars (emp κ ...)) (assertion-vars (κ ...))]
  [(assertion-vars ((p :-> y) κ ...))
   ,(cons (term (p-var p))
          (cons (term y)
                (term (assertion-vars (κ ...)))))]
  [(assertion-vars ((x = 0) κ ...))
   ,(cons (term x)
          (term (assertion-vars (κ ...))))]
  [(assertion-vars ((L [x ...] e) κ ...))
   ,(append (term [x ...])
            (term (assertion-vars (κ ...))))])

(define (list-subtract xs ys)
  (set->list (set-subtract (list->set xs) (list->set ys))))

(define-metafunction fun-SuSLik
  pat-vars : pat -> [x ...]
  [(pat-vars C) ()]
  [(pat-vars (C x ...)) [x ...]])

(define-metafunction fun-SuSLik
  layout-fn-vars : layout-fn-def -> [x ...]

  [(layout-fn-vars ((L : τ >-> layout [ x ... ]) ())) ()]

  [(layout-fn-vars ((L : τ >-> layout [ x ... ]) (pat → fs-assertion)))
   ,(list-subtract (term (assertion-vars fs-assertion)) (term (pat-vars pat)))]
  
  [(layout-fn-vars ((L : τ >-> layout [ x ... ]) ((pat → fs-assertion) layout-cases)))
   ,(append (term (layout-fn-vars ((L : τ >-> layout [ x ... ]) (pat → fs-assertion))))
            (term (layout-fn-vars ((L : τ >-> layout [x ...]) layout-cases))))])

(define-metafunction fun-SuSLik
  layout-freshen-free-vars : layout-fn-def -> layout-fn-def
  [(layout-freshen-free-vars ((L : τ >-> layout [x ...]) layout-cases))
   ((L : τ >-> layout [x ...])
    ,(let ((fvs (set->list (set-subtract (list->set (term (layout-fn-vars ((L : τ >-> layout [x ...]) layout-cases))))
                                         (list->set (term [x ...]))))))
       (term (substitute layout-cases
                         ,@(map list fvs (map gensym fvs))))))])

(define-judgment-form fun-SuSLik
  #:contract (reduce-layout-heaplet-inst Γ κ fs-assertion)
  #:mode (reduce-layout-heaplet-inst I I O)

  [-------------------
   (reduce-layout-heaplet-inst Γ emp (emp))]

  [-------------------
   (reduce-layout-heaplet-inst Γ (x = 0) ((x = 0)))]

  [-------------------
   (reduce-layout-heaplet-inst Γ (p :-> x) ((p :-> x)))]

  [-------------------
   (reduce-layout-heaplet-inst Γ (L [x ...] y) ((L [x ...] y)))]
  
  [
   (lookup Γ L layout-fn-def)
   #;(where layout-fn-def_fresh (layout-freshen-free-vars layout-fn-def))
   (lookup-layout-fn-case C
                          layout-fn-def
                          (e_L → (κ ...))
                          [z ...])
   #;(layout-inst-fn Γ [x ...] (substitute (layout-freshen-free-vars layout-fn-def) [z x] ...) (C e ...) fs-assertion)
   (layout-inst-fn Γ [z ...] layout-fn-def (C e ...) fs-assertion)
   -------------------
   (reduce-layout-heaplet-inst Γ (L [x ...] (C e ...)) (substitute fs-assertion [z x] ...))]


  )

; Reduce layout applications generated by an intermediate step
(define-judgment-form fun-SuSLik
  #:contract (reduce-layout-inst Γ fs-assertion fs-assertion)
  #:mode (reduce-layout-inst I I O)

  [-------------------
   (reduce-layout-inst Γ () ())]

  [(reduce-layout-heaplet-inst Γ κ (κ_new ...))
   (reduce-layout-inst Γ (κ_s ...) (κ_newS ...))
   -------------------
   (reduce-layout-inst Γ (κ κ_s ...) (κ_new ... κ_newS ...))
   ])

; This is the main judgment for translating layout functions being applied to ADT values
(define-judgment-form fun-SuSLik
  #:contract (layout-inst Γ [x ...] layout-case e fs-assertion)
  #:mode (layout-inst I I I I O)

  [-------------------
   (layout-inst Γ [x ...] (e → ()) e_2 (emp))]

  [(match-pat-con C e)
   (match-pat-con C e_2)
   -------------------
   (layout-inst Γ [x i ...] (e → (emp)) e_2 ((x = 0)))]

  [(match-pat-con C e)
   (match-pat-con C e_2)
   ; TODO: We need substitution here?
   (layout-inst Γ [x ...] (e → (κ ...)) e_2 (κ_2 ...))
   -------------------
   (layout-inst Γ [x ...] (e → ((p :-> z) κ ...)) e_2 ((p :-> z) κ_2 ...))]

  [(match-pat-con C e_2)
   (lookup Γ L layout-fn-def)
   (lookup-layout-fn-case C
                          layout-fn-def
                          (e_L → (κ_0 ...))
                          [z ...])
   (where (κ ...) ((substitute κ_0 [z y] ...) ...))
   (layout-pat-match [z ...] (e_L → (κ ...)) e_arg [x ...] (κ_2 ...))
   (layout-inst Γ [x ...] (e → (κ_3 ...)) e_2 (κ_r ...))
   (reduce-layout-inst Γ
                       (κ_2 ...)
                       fs-assertion)
   -------------------
   (layout-inst Γ
                [x ...]
                (e → ((L [y ...] e_arg) κ_3 ...))
                e_2
                fs-assertion)])

(define-judgment-form fun-SuSLik
  #:contract (layout-inst-app Γ [x ...] layout-fn-def e fs-assertion)
  #:mode (layout-inst-app I I I I O)

  [
   (layout-inst-fn Γ [x ...] layout-fn-def (C e_s ...) fs-assertion)
   -------------------
   (layout-inst-app Γ [x ...] layout-fn-def (C e_s ...) fs-assertion)]
  
  [-------------------
   (layout-inst-app Γ [x ...] layout-fn-def y ())]
)

(define-judgment-form fun-SuSLik
  #:contract (layout-inst-fn Γ [x ...] layout-fn-def e fs-assertion)
  #:mode (layout-inst-fn I I I I O)

  [(match-pat-con C e)
   #;(where layout-fn-def_fresh (layout-freshen-free-vars layout-fn-def))
   (lookup-layout-fn-case C layout-fn-def (e_L → (κ ...)) [x ...])

   (layout-pat-match [x ...] (e_L → (κ ...)) e [x ...] (κ_2 ...))
   (layout-inst Γ [x ...] (e_L → (κ_2 ...)) e fs-assertion)
   --------------------
   (layout-inst-fn Γ [x ...] layout-fn-def e fs-assertion)])

(define (defs ds)
  (if (null? ds)
      (term ·)
      (term (extend ,(defs (cdr ds)) ,(car ds)))))

(define List-ty (defs `[,(term (Nil : List)) ,(term (Cons : (Int → (List → List))))]))

(define sll-layout
  (term
   ((sll : List >-> layout [x])
    (
     (Nil → (emp))
     ((Cons head tail) →
       ((x :-> head) ((x + 1) :-> nxt) (sll [nxt] tail)))))))

(define sll-ctx (term (extend · sll ,sll-layout)))

(caching-enabled? #f) ; To freshen FVs in layout functions properly

(current-traced-metafunctions '(reduce-layout-inst))

(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b c)) fs-assertion) fs-assertion)
#;(judgment-holds (layout-inst-fn ,sll-ctx [x] ,sll-layout (Cons a (Cons b (Nil))) fs-assertion) fs-assertion)
