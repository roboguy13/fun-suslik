-- module FunSuSLik
--   where

  open import Data.List.Membership.Propositional using (_∈_)
  open import Agda.Builtin.Equality
  open import Relation.Binary.PropositionalEquality.Core
  open import Relation.Nullary
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.List
  open import Data.String hiding (_++_)
  open import Data.Integer
  open import Data.Product

  Scope = List String

  -- var : (x : String) → x ∈ s → Term s
  -- lam : (x : String) → Term (x ∷ s) → Term s
  -- app : Term s → Term s → Term s

  data Type : Set where
    Type-name : String → Type
    Int-Ty : Type
    Bool-Ty : Type
    _⇒_ : Type → Type → Type

  -- | Represented by its list of argument types, so that it is well-formed by construction
  Constructor-Type = List Type

  Constructor-Type→Type : Type → Constructor-Type → Type
  Constructor-Type→Type result-ty [] = result-ty
  Constructor-Type→Type result-ty (ty ∷ tys) = ty ⇒ (Constructor-Type→Type result-ty tys)

  data 𝒟-Alt : Set where
    mk-𝒟-Alt : String → Constructor-Type → 𝒟-Alt

  𝒟-Alts = List 𝒟-Alt
  Ctx = List String

  data 𝒟 : Set where
    mk-𝒟 : String → 𝒟-Alts → 𝒟

  data Has-𝒟 : 𝒟 → List 𝒟 → Set where
    Has-𝒟-here : ∀ d xs → Has-𝒟 d (d ∷ xs)
    Has-𝒟-there : ∀ d x xs → Has-𝒟 d xs → Has-𝒟 d (x ∷ xs)

  data FExpr (Σ : List 𝒟) (Γ : Ctx) : Set where
    FExpr-True : FExpr Σ Γ
    FExpr-False : FExpr Σ Γ

    FExpr-Int : ℤ → FExpr Σ Γ

    FExpr-let-in : (x : String) → FExpr Σ Γ → FExpr Σ (x ∷ Γ) → FExpr Σ Γ

    FExpr-if : FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ

    FExpr-var : (x : String) → x ∈ Γ → FExpr Σ Γ
    FExpr-lam : (x : String) → FExpr Σ (x ∷ Γ) → FExpr Σ Γ
    FExpr-app : FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ

    FExpr-fold : FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ

    FExpr-le : FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ
    FExpr-eq : FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ
    FExpr-add : FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ
    FExpr-sub : FExpr Σ Γ → FExpr Σ Γ → FExpr Σ Γ

  closed-FExpr : List 𝒟 → Set
  closed-FExpr Σ = FExpr Σ []

  -- | "Value judgment"
  data FExpr-val (Σ : List 𝒟) (Γ : Ctx) : FExpr Σ Γ → Set where
    True-val  : FExpr-val Σ Γ FExpr-True
    False-val : FExpr-val Σ Γ FExpr-False

    Int-val : ∀ i → FExpr-val Σ Γ (FExpr-Int i)
    lam-val : ∀ x e → FExpr-val Σ Γ (FExpr-lam x e)

  FExpr-val→FExpr : ∀ {Σ Γ e} → FExpr-val Σ Γ e → FExpr Σ Γ
  FExpr-val→FExpr {_} {_} {e} _ = e

  -- | Evaluation context that gives a CBV evaluation order
  data ℰ (Σ : List 𝒟) (Γ : Ctx) : (Γ-[] : Ctx) (A : FExpr Σ Γ-[]) → Set where
    ℰ[] : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A

    ℰ-app-1 : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-app-2 : ∀ {Γ-[] A} → ∀ {e : FExpr Σ Γ} → FExpr-val Σ Γ e → ℰ Σ Γ Γ-[] A → ℰ Σ Γ Γ-[] A

    ℰ-let-in-1 : ∀ {Γ-[] A} → (x : String)                             → ℰ Σ Γ Γ-[] A    → FExpr Σ (x ∷ Γ)    → ℰ Σ Γ Γ-[] A
    ℰ-let-in-2 : ∀ {Γ-[]}   → (x : String) → ∀ {A} → ∀ {e : FExpr Σ Γ} → FExpr-val Σ Γ e → ℰ Σ Γ (x ∷ Γ-[]) A → ℰ Σ Γ (x ∷ Γ-[]) A

    ℰ-fold-1 : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-fold-2 : ∀ {Γ-[] A} → ∀ {e} → FExpr-val Σ Γ e → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-fold-3 : ∀ {Γ-[] A} → ∀ {e₁ e₂} → FExpr-val Σ Γ e₁ → FExpr-val Σ Γ e₂ → ℰ Σ Γ Γ-[] A → ℰ Σ Γ Γ-[] A

    ℰ-if-1 : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-if-True  : ∀ {Γ-[] A} → FExpr-val Σ Γ FExpr-True  → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-if-False : ∀ {Γ-[] A} → FExpr-val Σ Γ FExpr-False → FExpr Σ Γ → ℰ Σ Γ Γ-[] A → ℰ Σ Γ Γ-[] A

    ℰ-le-1 : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-le-2 : ∀ {Γ-[] A} → ∀ {e} → FExpr-val Σ Γ e → ℰ Σ Γ Γ-[] A → ℰ Σ Γ Γ-[] A

    ℰ-eq-1 : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-eq-2 : ∀ {Γ-[] A} → ∀ {e} → FExpr-val Σ Γ e → ℰ Σ Γ Γ-[] A → ℰ Σ Γ Γ-[] A

    ℰ-add-1 : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-add-2 : ∀ {Γ-[] A} → ∀ {e} → FExpr-val Σ Γ e → ℰ Σ Γ Γ-[] A → ℰ Σ Γ Γ-[] A

    ℰ-sub-1 : ∀ {Γ-[] A} → ℰ Σ Γ Γ-[] A → FExpr Σ Γ → ℰ Σ Γ Γ-[] A
    ℰ-sub-2 : ∀ {Γ-[] A} → ∀ {e} → FExpr-val Σ Γ e → ℰ Σ Γ Γ-[] A → ℰ Σ Γ Γ-[] A

  FExpr→ℰ : ∀ {Σ Γ} → FExpr Σ Γ → ∃[ h ] (ℰ Σ Γ Γ h)
  FExpr→ℰ {Σ} {Γ} FExpr-True = FExpr-True , ℰ[]
  FExpr→ℰ {Σ} {Γ} FExpr-False = FExpr-True , ℰ[]
  FExpr→ℰ {Σ} {Γ} (FExpr-Int x) = FExpr-True , ℰ[]
  FExpr→ℰ {Σ} {Γ} (FExpr-let-in x e e₁) = e , ℰ-let-in-1 x ℰ[] e₁
  FExpr→ℰ {Σ} {Γ} (FExpr-if c e₁ e₂) = c , ℰ-if-1 ℰ[] e₁ e₂
  FExpr→ℰ {Σ} {Γ} (FExpr-var x x₁) = FExpr-var x x₁ , ℰ[]
  FExpr→ℰ {Σ} {Γ} (FExpr-lam x e) = FExpr-lam x e , ℰ[]
  FExpr→ℰ {Σ} {Γ} (FExpr-app e e₁) = e , ℰ-app-1 ℰ[] e₁
  FExpr→ℰ {Σ} {Γ} (FExpr-fold e e₁ e₂) = e , ℰ-fold-1 ℰ[] e₁ e₂
  FExpr→ℰ {Σ} {Γ} (FExpr-le e e₁) = e , ℰ-le-1 ℰ[] e₁
  FExpr→ℰ {Σ} {Γ} (FExpr-eq e e₁) = e , ℰ-eq-1 ℰ[] e₁
  FExpr→ℰ {Σ} {Γ} (FExpr-add e e₁) = e , ℰ-add-1 ℰ[] e₁
  FExpr→ℰ {Σ} {Γ} (FExpr-sub e e₁) = e , ℰ-sub-1 ℰ[] e₁

  -- []-closed-ℰ→FExpr : ∀ {Σ Γ h} → ℰ Σ Γ Γ h → FExpr Σ Γ
  -- []-closed-ℰ→FExpr {_} {_} {h} ℰ[] = h
  -- []-closed-ℰ→FExpr (ℰ-app-1 ev x) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-app-2 x ev) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-let-in-1 x ev x₁) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-fold-1 ev x x₁) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-fold-2 x ev x₁) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-fold-3 x x₁ ev) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-if-1 ev x x₁) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-if-True x ev x₁) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-if-False x x₁ ev) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-le-1 ev x) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-le-2 x ev) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-eq-1 ev x) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-eq-2 x ev) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-add-1 ev x) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-add-2 x ev) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-sub-1 ev x) = {!!}
  -- []-closed-ℰ→FExpr (ℰ-sub-2 x ev) = {!!}

  -- ℰ→FExpr : ∀ {Σ Γ Γ-[] h} → ℰ Σ Γ Γ-[] h → FExpr Σ Γ
  -- ℰ→FExpr {Σ} {Γ} {Γ-[]} {h} ℰ[] = h
  -- ℰ→FExpr (ℰ-app-1 ev x) = FExpr-app (ℰ→FExpr ev) x
  -- ℰ→FExpr (ℰ-app-2 x ev) = FExpr-app (FExpr-val→FExpr x) (ℰ→FExpr ev)
  -- ℰ→FExpr (ℰ-let-in-1 x ev x₁) = FExpr-let-in x (ℰ→FExpr ev) x₁
  -- ℰ→FExpr (ℰ-let-in-2 x x₁ ev) = FExpr-let-in x (FExpr-val→FExpr x₁) (ℰ→FExpr ev)
  -- ℰ→FExpr (ℰ-fold-1 ev x x₁) = {!!}
  -- ℰ→FExpr (ℰ-fold-2 x ev x₁) = {!!}
  -- ℰ→FExpr (ℰ-fold-3 x x₁ ev) = {!!}
  -- ℰ→FExpr (ℰ-if-1 ev x x₁) = {!!}
  -- ℰ→FExpr (ℰ-if-True x ev x₁) = {!!}
  -- ℰ→FExpr (ℰ-if-False x x₁ ev) = {!!}
  -- ℰ→FExpr (ℰ-le-1 ev x) = {!!}
  -- ℰ→FExpr (ℰ-le-2 x ev) = {!!}
  -- ℰ→FExpr (ℰ-eq-1 ev x) = {!!}
  -- ℰ→FExpr (ℰ-eq-2 x ev) = {!!}
  -- ℰ→FExpr (ℰ-add-1 ev x) = {!!}
  -- ℰ→FExpr (ℰ-add-2 x ev) = {!!}
  -- ℰ→FExpr (ℰ-sub-1 ev x) = {!!}
  -- ℰ→FExpr (ℰ-sub-2 x ev) = {!!}

  contract-list-under : ∀ {Γ : Ctx} → ∀ {prefix x y} → x ∈ (prefix ++ y ∷ y ∷ Γ) → x ∈ (prefix ++ y ∷ Γ)
  contract-list-under {Γ} {[]} {x} {y} (here px) = here px
  contract-list-under {Γ} {[]} {x} {y} (there prf) = prf
  contract-list-under {Γ} {x₁ ∷ prefix} {x} {y} (here px) = here px
  contract-list-under {Γ} {x₁ ∷ prefix} {x} {y} (there prf) = there (contract-list-under prf)

  contract-under : ∀ {Σ Γ x prefix} → FExpr Σ (prefix ++ (x ∷ x ∷ Γ)) → FExpr Σ (prefix ++ (x ∷ Γ))
  contract-under FExpr-True = FExpr-True
  contract-under FExpr-False = FExpr-False
  contract-under (FExpr-Int i) = FExpr-Int i
  contract-under {Σ} {Γ} {x} {prefix} (FExpr-let-in y e e₁) = FExpr-let-in y (contract-under e) (contract-under {_} {_} {_} {y ∷ prefix} e₁)
  contract-under (FExpr-if e e₁ e₂) = FExpr-if (contract-under e) (contract-under e₁) (contract-under e₂)
  contract-under {_} {_} {x} {[]} (FExpr-var y prf) with prf
  ... | here px = FExpr-var y (here px)
  ... | there z = FExpr-var y z
  contract-under {Σ} {Γ} {x} {x₁ ∷ prefix} (FExpr-var y prf) with prf
  ... | here px = FExpr-var y (here px)
  ... | there z = FExpr-var y (contract-list-under {Γ} {x₁ ∷ prefix} prf)
  contract-under {_} {Γ} {x} {prefix} (FExpr-lam y e) = FExpr-lam y (contract-under {_} {_} {_} {y ∷ prefix} e)
  contract-under (FExpr-app e e₁) = FExpr-app (contract-under e) (contract-under e₁)
  contract-under (FExpr-fold e e₁ e₂) = FExpr-fold (contract-under e) (contract-under e₁) (contract-under e₂)
  contract-under (FExpr-le e e₁) = FExpr-le (contract-under e) (contract-under e₁)
  contract-under (FExpr-eq e e₁) = FExpr-eq (contract-under e) (contract-under e₁)
  contract-under (FExpr-add e e₁) = FExpr-add (contract-under e) (contract-under e₁)
  contract-under (FExpr-sub e e₁) = FExpr-sub (contract-under e) (contract-under e₁)

  contract : ∀ {Σ Γ x} → FExpr Σ (x ∷ x ∷ Γ) → FExpr Σ (x ∷ Γ)
  contract FExpr-True = FExpr-True
  contract FExpr-False = FExpr-False
  contract (FExpr-Int i) = FExpr-Int i
  contract (FExpr-let-in y e e₁) = FExpr-let-in y (contract e) (contract-under {_} {_} {_} {[ y ]} e₁)
  contract (FExpr-if e e₁ e₂) = FExpr-if (contract e) (contract e₁) (contract e₂)
  contract (FExpr-var y (here px)) = FExpr-var y (here px)
  contract (FExpr-var y (there prf)) = FExpr-var y prf
  contract (FExpr-lam y e) = FExpr-lam y (contract-under {_} {_} {_} {[ y ]} e)
  contract (FExpr-app e e₁) = FExpr-app (contract e) (contract e₁)
  contract (FExpr-fold e e₁ e₂) = FExpr-fold (contract e) (contract e₁) (contract e₂)
  contract (FExpr-le e e₁) = FExpr-le (contract e) (contract e₁)
  contract (FExpr-eq e e₁) = FExpr-eq (contract e) (contract e₁)
  contract (FExpr-add e e₁) = FExpr-add (contract e) (contract e₁)
  contract (FExpr-sub e e₁) = FExpr-sub (contract e) (contract e₁)

  swap-Γ : ∀ {Σ Γ x y} → FExpr Σ (x ∷ y ∷ Γ) → FExpr Σ (y ∷ x ∷ Γ)
  swap-Γ FExpr-True = FExpr-True
  swap-Γ FExpr-False = FExpr-True
  swap-Γ (FExpr-Int x) = FExpr-True
  swap-Γ (FExpr-let-in x e e₁) = FExpr-True
  swap-Γ (FExpr-if e e₁ e₂) = FExpr-True
  swap-Γ (FExpr-var x x₁) = FExpr-True
  swap-Γ (FExpr-lam x e) = FExpr-True
  swap-Γ (FExpr-app e e₁) = FExpr-True
  swap-Γ (FExpr-fold e e₁ e₂) = FExpr-True
  swap-Γ (FExpr-le e e₁) = FExpr-True
  swap-Γ (FExpr-eq e e₁) = FExpr-True
  swap-Γ (FExpr-add e e₁) = FExpr-True
  swap-Γ (FExpr-sub e e₁) = FExpr-True

  weaken : ∀ {Σ Γ x} → FExpr Σ Γ → FExpr Σ (x ∷ Γ)
  weaken FExpr-True = FExpr-True
  weaken FExpr-False = FExpr-False
  weaken (FExpr-Int i) = FExpr-Int i
  weaken {_} {_} {x} (FExpr-let-in y e e₁) = FExpr-let-in y (weaken e) (swap-Γ (weaken e₁))
  weaken (FExpr-if e e₁ e₂) = FExpr-if (weaken e) (weaken e₁) (weaken e₂)
  weaken (FExpr-var y prf) = FExpr-var y (there prf)
  weaken (FExpr-lam y e) = FExpr-lam y (swap-Γ (weaken e))
  weaken (FExpr-app e e₁) = FExpr-app (weaken e) (weaken e₁)
  weaken (FExpr-fold e e₁ e₂) = FExpr-fold (weaken e) (weaken e₁) (weaken e₂)
  weaken (FExpr-le e e₁) = FExpr-le (weaken e) (weaken e₁)
  weaken (FExpr-eq e e₁) = FExpr-eq (weaken e) (weaken e₁)
  weaken (FExpr-add e e₁) = FExpr-add (weaken e) (weaken e₁)
  weaken (FExpr-sub e e₁) = FExpr-sub (weaken e) (weaken e₁)

  data SubstHere {Σ x} : (Γ : Ctx) (s : FExpr Σ Γ) → FExpr Σ (x ∷ Γ) → FExpr Σ Γ → Set where
    SubstHere-True : ∀ {Γ s} → SubstHere Γ s FExpr-True FExpr-True
    SubstHere-False : ∀ {Γ s} → SubstHere Γ s FExpr-False FExpr-False

    SubstHere-Int : ∀ {Γ s} → ∀ {i} → SubstHere Γ s (FExpr-Int i) (FExpr-Int i)

    SubstHere-let-in-≡ : ∀ {Γ s} → ∀ {e e' e₁} →
      SubstHere Γ s e e' →
      SubstHere Γ s (FExpr-let-in x e e₁) (FExpr-let-in x e' (contract e₁))

    SubstHere-let-in-≢ : ∀ {Γ s} → ∀ {y e e' e₁ e₁'} →
      y ≢ x →
      SubstHere Γ s e e' →
      SubstHere (y ∷ Γ) (weaken s) (swap-Γ e₁) e₁' →
      SubstHere Γ s (FExpr-let-in y e e₁) (FExpr-let-in y e' e₁')

    SubstHere-weaken-swap : ∀ {Γ s} → ∀ {x e₁ e₁'} →
      SubstHere (x ∷ Γ) (weaken {_} {Γ} {x} s) (swap-Γ e₁) e₁'

    SubstHere-if : ∀ {Γ s} → ∀ {x y z x' y' z'} →
      SubstHere Γ s x x' →
      SubstHere Γ s y y' →
      SubstHere Γ s z z' →
      SubstHere Γ s (FExpr-if x y z) (FExpr-if x' y' z')

    SubstHere-var-≡ : ∀ {Γ s} → ∀ {prf} →
      SubstHere Γ s (FExpr-var x prf) s

    SubstHere-var-≢ : ∀ {Γ s} → ∀ {y prf} →
      y ≢ x →
      SubstHere Γ s (FExpr-var y (there prf)) (FExpr-var y prf)

    SubstHere-lam-≡ : ∀ {Γ s} → ∀ {e} →
      SubstHere Γ s (FExpr-lam x e) (FExpr-lam x (contract e))

    SubstHere-lam-≢ : ∀ {Γ s} → ∀ {y e e'} →
      y ≢ x →
      SubstHere Γ s e e' →
      SubstHere Γ s (FExpr-lam y (weaken e)) (FExpr-lam y (weaken e'))

  SubstHere-exists : ∀ {Σ Γ x} → ∀ s → ∀ (e : FExpr Σ (x ∷ Γ)) → ∃[ e' ] (SubstHere Γ s e e')
  SubstHere-exists {_} {_} {x} s FExpr-True = FExpr-True , SubstHere-True
  SubstHere-exists {_} {_} {x} s FExpr-False = FExpr-False , SubstHere-False
  SubstHere-exists {_} {_} {x} s (FExpr-Int x₁) = FExpr-Int x₁ , SubstHere-Int
  SubstHere-exists {_} {_} {x} s (FExpr-let-in y e e₁) with x Data.String.≟ y
  ... | yes prf rewrite prf =
    let subst-e = SubstHere-exists s e
    in
    FExpr-let-in y (proj₁ subst-e) (contract e₁) , SubstHere-let-in-≡ (proj₂ subst-e)
  ... | no ¬prf =
    let subst-e = SubstHere-exists s e
        subst-e₁ = {!!}
    in
    FExpr-let-in y (proj₁ subst-e) {!!} , {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-if e e₁ e₂) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-var x₁ x₂) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-lam x₁ e) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-app e e₁) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-fold e e₁ e₂) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-le e e₁) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-eq e e₁) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-add e e₁) = {!!}
  SubstHere-exists {_} {_} {x} s (FExpr-sub e e₁) = {!!}

  -- subst-here : ∀ {Σ Γ x} → FExpr Σ (x ∷ Γ) → FExpr Σ Γ
  -- subst-here FExpr-True = FExpr-True
  -- subst-here FExpr-False = FExpr-False
  -- subst-here (FExpr-Int i) = FExpr-Int i
  -- subst-here {Σ} {Γ} {x} (FExpr-let-in y e e₁) with x Data.String.≟ y
  -- ... | yes prf rewrite prf = FExpr-let-in y (subst-here e) (contract e₁)
  -- ... | no ¬prf = FExpr-let-in y {!!} (subst-here (swap-Γ e₁))
  -- subst-here (FExpr-if e e₁ e₂) = {!!}
  -- subst-here (FExpr-var x x₁) = {!!}
  -- subst-here (FExpr-lam x e) = {!!}
  -- subst-here (FExpr-app e e₁) = {!!}
  -- subst-here (FExpr-fold e e₁ e₂) = {!!}
  -- subst-here (FExpr-le e e₁) = {!!}
  -- subst-here (FExpr-eq e e₁) = {!!}
  -- subst-here (FExpr-add e e₁) = {!!}
  -- subst-here (FExpr-sub e e₁) = {!!}

  data _⟼ₐ_ {Σ : List 𝒟} : {Γ Γ' : Ctx} → FExpr Σ Γ → FExpr Σ Γ' → Set where
    -- app-lam : ∀ {Γ Γ' x} → ∀ e → ∀ {e₂} → FExpr-val Σ Γ e₂ → (FExpr-app (FExpr-lam x e) e₂) ⟼ₐ subst here e₂ e


  -- reduce-ℰ : ∀ {Σ Γ Γ-[] Γ-[]' e e'} → (e ⟼ₐ e') → ℰ Σ Γ Γ-[] e → ℰ Σ Γ Γ-[]' e'
  -- reduce-ℰ prf x = ℰ[]

  -- data _⟶ℰ_ {Σ : List 𝒟} {Γ : Ctx} : ℰ Σ Γ → ℰ Σ Γ → Set where
    -- reduce-ℰ : ∀ (e e' : FExpr Σ Γ) → (e ⟶ₐ e') → (ℰ Σ Γ e ⟶ ℰ Σ Γ e')


  -- ⟼
