#lang racket
(require redex)
#;(require racket/set)

(define-language fun-SuSLik
  (data-def ::= (data D where alt ...))
  (alt ::= (C τ ...))
  (τ ::= Int Bool (τ → τ) D)
  (Γ ::= · (extend Γ (x : τ)) (extend Γ L layout-fn-def))
  (fn-def ::= ((f : τ) (fn-case ...)))
  (fn-case ::= (pat guarded-expr guarded-expr ...))
  (guarded-expr ::= [bool-expr → e])
  (match-case ::= (pat → e))
  (match-cases ::= match-case (match-case match-cases))
  (layout-fn-def ::= ((L : τ >-> layout [ x ... ]) layout-cases))
  (layout-case ::= ([x ...] pat → fs-assertion))
  (layout-cases ::= layout-case (layout-case layout-cases))

  (fs-heaplet κ ::= emp (p :-> pointed-to) (p = equals-val) layout-app)

  (layout-app ::= (L [x ...] layout-arg))
  (fs-assertion ::= (fs-heaplet ...))
  (lower-app (lower [x ...] L e))

  (instantiate-app (instantiate L L f))

  (layout-arg ::= y constr-app lower-app)
  (pat ::= C (C x ...))
  (p ::= x (x + n))
  (n ::= natural)
  (I ::= integer)
  (B ::= false true)
  (pointed-to ::= base-val x)
  (base-val ::= integer B)
  (D a b f g h x y z i j k ::= variable-not-otherwise-mentioned)
  (L ::= (variable-prefix L-))
  (C ::= (variable-prefix C-))
  )

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
