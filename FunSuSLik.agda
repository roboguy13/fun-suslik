open import Data.Sum
open import Data.Product
open import Data.List
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All
open import Data.Nat
open import Data.Bool
open import Data.Integer
open import Function.Base using (case_of_; case_return_of_)

open ≡-Reasoning


module FunSuSLik
  (Name : Set)
  (Name-eq-dec : ∀ {a b : Name} → (a ≡ b) ⊎ (a ≢ b))
  (let _N=_ : ∀ (a b : Name) → Set; a N= b = case (Name-eq-dec {a} {b}) of λ { (inj₁ prf) → ⊤ ; (inj₂ ref) → ⊥ })
  (let Params : Set ; Params = List Name)
  (let _N∈_ : Name → Params → Set ; x N∈ xs = Any (_N= x) xs)
  (fresh : ∀ env → Σ Name λ n → All (_≢ n) env)
  -- (fresh-Name : (xs : Params) → Σ Name λ n → ¬ (n N∈ xs))
  where

Name-N=-≡ : ∀ {a : Name} → a N= a
Name-N=-≡ {a} with Name-eq-dec {a} {a}
... | inj₁ x = tt
... | inj₂ y = y refl

-- Valid-Param : Name → Params → Set
-- Valid-Param (Mk-Name n) (Mk-Params p) = n Data.Nat.< p

-- Name : Set
-- Name = ℕ

data Addr : Set where
  _:+_ : Name → ℕ → Addr
  Unused-Addr : Addr -- TODO: Figure this out in more detail

data Expr : Set

data Heaplet : Set where
  _:->_ : Addr → Expr → Heaplet
  _H·_ : Name → Expr → Heaplet


data Layout-Branch : Set where
  Mk-Layout-Branch :
    Name →         -- Constructor name
    Params →       -- Formal parameters
    List Heaplet → -- Body
    Layout-Branch

data Layout : Set where
  Mk-Layout : List Layout-Branch → Layout

-- fun-SuSLik Language
data Type : Set where
  Int-Type : Type
  Bool-Type : Type
  _⟶_ : Type → Type → Type
  Adt-Type : Name → Type
  Layout-Type : Layout → Type

data Expr where
  Var : Name → Expr
  _C·_ : Name → List Expr → Expr
  _·_ : Name → Expr → Expr

  Bool-Lit : Bool → Expr
  Int-Lit : ℤ → Expr

  -- _&&_ : Expr → Expr → Expr
  -- Not : Expr → Expr

  _==_ : Expr → Expr → Expr

  Add : Expr → Expr → Expr
  -- Mul : Expr → Expr → Expr

  Lower : Layout → Expr → Expr
  Instantiate :
    Layout → -- Input layout
    Layout → -- Output layout
    Name → -- Function name
    Expr → -- Argument
    Expr

  Lift : Addr → Expr -- Only for internal use


data Guard-Branch : Set where
  Mk-Guard-Branch :
    Expr → -- Boolean guard
    Expr → -- RHS
    Guard-Branch

data Fn-Branch : Set where
  Mk-Fn-Branch :
    Name →       -- Constructor name
    Params →            -- Pattern variables
    List Guard-Branch → -- Guarded RHS's
    Fn-Branch

data Fn-Def : Set where
  Mk-Fn-Def : List Fn-Branch → Fn-Def

-- SuSLik Language
data SuSLik-Expr : Set where
  Var : Name → SuSLik-Expr
  Addr-Var : Addr → SuSLik-Expr

  Bool-Lit : Bool → SuSLik-Expr
  Int-Lit : ℤ → SuSLik-Expr

  _&&_ : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr
  Not : SuSLik-Expr → SuSLik-Expr

  _==_ : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr

  Add : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr
  -- Mul : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr

data SuSLik-Heaplet : Set where
  _:->_ : Addr → SuSLik-Expr → SuSLik-Heaplet
  _·_ : Name → List SuSLik-Expr → SuSLik-Heaplet
  Temp : Addr → SuSLik-Heaplet

data SuSLik-Asn : Set where
  _,,_ :
    SuSLik-Expr → -- Pure part
    List SuSLik-Heaplet → -- Spatial part
    SuSLik-Asn

-- Generate SuSLik inductive predicate names for instantiated functions
postulate
  I : Layout → Layout → Name → Name
  I-uniq : ∀ {A₁ B₁ A₂ B₂ f g} →
    (A₁ ≢ A₂) ⊎ (B₁ ≢ B₂) ⊎ (f ≢ g) →
    I A₁ B₁ f ≢ I A₂ B₂ g

infixr 20 _<>_
_<>_ : SuSLik-Asn → SuSLik-Asn → SuSLik-Asn
(x₁ ,, x₂) <> (y₁ ,, y₂) =
  (x₁ && y₁) ,, (x₂ Data.List.++ y₂)

data Append {A : Set} : List A → List A → List A → Set where
  Append-Nil : ∀ {xs} → Append [] xs xs
  Append-Cons : ∀ {x xs ys zs} →
    Append xs ys zs →
    Append (x ∷ xs) ys (x ∷ zs)

Append-++ : ∀ {A : Set} {x y z : List A} →
  Append x y z →
  x ++ y ≡ z
Append-++ Append-Nil = refl
Append-++ (Append-Cons prf) rewrite Append-++ prf = refl

Append-exists : ∀ {A : Set} {xs ys : List A} →
  Append xs ys (xs ++ ys)
Append-exists {_} {[]} {ys} = Append-Nil
Append-exists {_} {x ∷ xs} {ys} = Append-Cons Append-exists

data Combine-Asns : SuSLik-Asn → SuSLik-Asn → SuSLik-Asn → Set where
  Mk-Combine-Asns : ∀ {x₁ x₂ y₁ y₂ appended} →
    Append x₂ y₂ appended →
    Combine-Asns (x₁ ,, x₂) (y₁ ,, y₂) ((x₁ && y₁) ,, appended)

Combine-Asns-<> : ∀ {x y z} →
  Combine-Asns x y z →
  x <> y ≡ z
Combine-Asns-<> (Mk-Combine-Asns prf) rewrite Append-++ prf = refl

Combine-Asns-exists : ∀ {x y} →
  Combine-Asns x y (x <> y)
Combine-Asns-exists {x ,, x₁} {x₂ ,, x₃} = Mk-Combine-Asns Append-exists

pure-prop : SuSLik-Expr → SuSLik-Asn
pure-prop e = e ,, []

spatial-prop : List SuSLik-Heaplet → SuSLik-Asn
spatial-prop hs = Bool-Lit true ,, hs


data SuSLik-Ind-Branch : Set where
  Mk-SuSLik-Ind-Branch :
    SuSLik-Expr → -- Condition
    SuSLik-Asn →  -- RHS
    SuSLik-Ind-Branch

data SuSLik-Ind : Set where
  Mk-SuSLik-Ind :
    Params →
    List SuSLik-Ind-Branch →
    SuSLik-Ind

-- data Global-Def : Set where
--   Global-Fn : Fn-Def → Global-Def
--   Global-Layout : Layout → Global-Def

-- -- Global environment
-- G-Env : Set
-- G-Env = List (Name × Global-Def × Type)

Ty-Env : Set
Ty-Env = List (Name × Type)

G-Env : Set
G-Env = List (Name × Fn-Def)

-- SuSLik-Env : Set
-- SuSLik-Env = List SuSLik-Expr

-- data Env-lookup : Name → Env → (Expr × Type) → Set where
--   Env-here : ∀ {x xs} → Env-lookup (Mk-Name 0) (x ∷ xs) x
--   Env-there : ∀ {n x xs e} →
--     Env-lookup (Mk-Name n) xs e →
--     Env-lookup (Mk-Name (ℕ.suc n)) (x ∷ xs) e

-- data G-Env-lookup : Global-Name → G-Env → (Global-Def × Type) → Set where
--   G-Env-here : ∀ {n xs d} → G-Env-lookup n ((n , d) ∷ xs) d
--   G-Env-there : ∀ {n x xs d} →
--     G-Env-lookup n xs d →
--     G-Env-lookup n (x ∷ xs) d

data Base-Type : Type → Set where
  Base-Type-Int : Base-Type Int-Type
  Base-Type-Bool : Base-Type Bool-Type

-- -- TODO: Make this a tree (or a "bunch")?
-- Fresh-Supply : Set
-- Fresh-Supply = List Name

data Fresh-Supply : Set where
  FS-Empty : Fresh-Supply
  FS-Branch : List Name → Fresh-Supply → Fresh-Supply → Fresh-Supply

data FS-All (P : Name → Set) : Fresh-Supply → Set where
  FS-All-Empty : FS-All P FS-Empty
  FS-All-Branch : ∀ {xs left right} →
    All P xs →
    FS-All P left →
    FS-All P right →
    FS-All P (FS-Branch xs left right)

data FS-Any (P : Name → Set) : Fresh-Supply → Set where
  FS-Here : ∀ {xs left right} →
    Any P xs →
    FS-Any P (FS-Branch xs left right)

  FS-Left : ∀ {xs left right} →
    FS-Any P left →
    FS-Any P (FS-Branch xs left right)

  FS-Right : ∀ {xs left right} →
    FS-Any P right →
    FS-Any P (FS-Branch xs left right)

data _,,_▷_⇓[_,_]_ : Fresh-Supply → G-Env → Expr → Addr → Name → SuSLik-Asn → Set where
  ⇓-Var : ∀ {Σ x r v} →
    FS-Empty ,, Σ ▷ Var x ⇓[ r , v ] ((Var v == Var x) ,, [ r :-> Var v ])

  ⇓-Int : ∀ {Σ i r v} →
    FS-Empty ,, Σ ▷ Int-Lit i ⇓[ r , v ] ((Var v == Int-Lit i) ,, [ r :-> Var v ])

  ⇓-Bool : ∀ {Σ b r v} →
    FS-Empty ,, Σ ▷ Bool-Lit b ⇓[ r , v ] ((Var v == Bool-Lit b) ,, [ r :-> Var v ])

  ⇓-Add : ∀ {fr₁ fr₂ Σ e₁ e₂ r v v₁ v₂ s₁ s₂ s₃ s} →
    v₁ ≢ v →
    v₂ ≢ v →
    v₁ ≢ v₂ →
    Combine-Asns s₁ s₂ s₃ →
    Combine-Asns ((Var v == Add (Var v₁) (Var v₂)) ,, []) s₃ s →
    fr₁ ,, Σ ▷ e₁ ⇓[ Unused-Addr , v₁ ] s₁ →
    fr₂ ,, Σ ▷ e₂ ⇓[ Unused-Addr , v₂ ] s₂ →
    FS-Branch (v₁ ∷ v₂ ∷ []) fr₁ fr₂ ,, Σ ▷ (Add e₁ e₂) ⇓[ r , v ] s

  ⇓-== : ∀ {fr₁ fr₂ Σ e₁ e₂ r v v₁ v₂ s₁ s₂ s₃ s} →
    v₁ ≢ v →
    v₂ ≢ v →
    v₂ ≢ v₁ →
    Combine-Asns s₁ s₂ s₃ →
    Combine-Asns ((Var v == ((Var v₁) == (Var v₂))) ,, []) s₃ s →
    fr₁ ,, Σ ▷ e₁ ⇓[ Unused-Addr , v₁ ] s₁ →
    fr₂ ,, Σ ▷ e₂ ⇓[ Unused-Addr , v₂ ] s₂ →
    FS-Branch (v₁ ∷ v₂ ∷ []) fr₁ fr₂ ,, Σ ▷ (e₁ == e₂) ⇓[ r , v ] s

  -- ⇓-Not : ∀ {fr₁ Σ e₁ r v v₁ s₁} →
  --   v₁ ≢ v →
  --   fr₁ ,, Σ ▷ e₁ ⇓[ Unused-Addr , v₁ ] s₁ →
  --   FS-Branch (v₁ ∷ []) fr₁ FS-Empty ,, Σ ▷ (Not e₁) ⇓[ r , v ] (((Var v == Not (Var v₁)) ,, [])
  --                                  <> s₁)


  ⇓-Instantiate : ∀ {fr Σ A B f e x r v v₁ s₁ s} →
    v ≢ v₁ →
    Combine-Asns (Bool-Lit true ,, ((I A B f · (Addr-Var r ∷ Var v ∷ [])) ∷ (r :-> Var v) ∷ [])) s₁ s →
    FS-Branch (x ∷ v₁ ∷ []) fr FS-Empty ,, Σ ▷ (Lower A e) ⇓[ x :+ 0 , v₁ ] s₁ →
    FS-Branch (x ∷ v₁ ∷ []) fr FS-Empty ,, Σ ▷ (Instantiate A B f e) ⇓[ r , v ] s

  ⇓-Lower-Lower : ∀ {fr Σ A e r v s} →
    fr ,, Σ ▷ (Lower A e) ⇓[ r , v ] s →
    fr ,, Σ ▷ (Lower A (Lower A e)) ⇓[ r , v ] s

--   -- ⇓-Lower-C : ∀ {Σ A C es }

  ⇓-Instantiate-Comp : ∀ {fr₁ fr₂ Σ A B C f g e r v t s₁ s₂ s₃ s v₁} →
    v ≢ v₁ →
    Combine-Asns s₁ s₂ s₃ →
    Combine-Asns (spatial-prop [ Temp (t :+ 0) ]) s₃ s →
    fr₁ ,, Σ ▷ (Instantiate B C f (Lift (t :+ 0))) ⇓[ r , v ] s₁ →
    fr₂ ,, Σ ▷ (Instantiate A B g e) ⇓[ t :+ 0 , v₁ ] s₂ →
    FS-Branch (t ∷ v₁ ∷ []) fr₁ fr₂ ,, Σ ▷ (Instantiate B C f (Instantiate A B g e)) ⇓[ r , v ] s

  ⇓-Lift : ∀ {Σ s r v} →
    FS-Empty ,, Σ ▷ (Lift s) ⇓[ r , v ] (((Var v == Addr-Var r) && (Addr-Var r == Addr-Var s)) ,, [])

-- Subst : Set
-- Subst = List (Name × Name)

-- Subst-Name-1 : (Name × Name) → Name → Name
-- Subst-Name-1 (old , new) x with Name-eq-dec {old} {x}
-- ... | inj₁ refl = new
-- ... | inj₂ y = x

-- Subst-Name : Subst → Name → Name
-- Subst-Name [] n = n
-- Subst-Name (x ∷ xs) n = Subst-Name-1 x (Subst-Name xs n)

-- Subst-Addr-1 : (Name × Name) → Addr → Addr
-- Subst-Addr-1 subst (x :+ x₁) = Subst-Name-1 subst x :+ x₁
-- Subst-Addr-1 subst Unused-Addr = Unused-Addr

-- Subst-Addr : Subst → Addr → Addr
-- Subst-Addr [] addr = addr
-- Subst-Addr (x ∷ xs) addr = Subst-Addr xs (Subst-Addr-1 x addr)

-- Subst-Exprs-1 : (Name × Name) → List Expr → List Expr

-- Subst-Expr-1 : (Name × Name) → Expr → Expr
-- Subst-Expr-1 subst (Var x) = Var (Subst-Name-1 subst x)
-- Subst-Expr-1 subst (x C· ys) = x C· (Subst-Exprs-1 subst ys)
-- Subst-Expr-1 subst (x · e) = x · (Subst-Expr-1 subst e)
-- Subst-Expr-1 subst (Bool-Lit x) = Bool-Lit x
-- Subst-Expr-1 subst (Int-Lit x) = Int-Lit x
-- Subst-Expr-1 subst (e && e₁) = (Subst-Expr-1 subst e) && (Subst-Expr-1 subst e₁)
-- Subst-Expr-1 subst (Not e) = Not (Subst-Expr-1 subst e)
-- Subst-Expr-1 subst (e == e₁) = (Subst-Expr-1 subst e) == (Subst-Expr-1 subst e₁)
-- Subst-Expr-1 subst (Add e e₁) = Add (Subst-Expr-1 subst e) (Subst-Expr-1 subst e₁)
-- Subst-Expr-1 subst (Lower x e) = Lower x (Subst-Expr-1 subst e)
-- Subst-Expr-1 subst (Instantiate A B f e) = Instantiate A B f (Subst-Expr-1 subst e)
-- Subst-Expr-1 subst (Lift x) = Lift (Subst-Addr-1 subst x)

-- Subst-Exprs-1 subst [] = []
-- Subst-Exprs-1 subst (x ∷ xs) = Subst-Expr-1 subst x ∷ Subst-Exprs-1 subst xs

-- Subst-Expr : Subst → Expr → Expr
-- Subst-Expr [] e = e
-- Subst-Expr (x ∷ xs) e = Subst-Expr-1 x (Subst-Expr xs e)

-- Subst-SuSLik-Expr-1 : (Name × Name) → SuSLik-Expr → SuSLik-Expr
-- Subst-SuSLik-Expr-1 subst (Var x) = Var (Subst-Name-1 subst x)
-- Subst-SuSLik-Expr-1 subst (Addr-Var addr) = Addr-Var (Subst-Addr-1 subst addr)
-- Subst-SuSLik-Expr-1 (old , new) (Bool-Lit x) = Bool-Lit x
-- Subst-SuSLik-Expr-1 (old , new) (Int-Lit x) = Int-Lit x
-- Subst-SuSLik-Expr-1 subst (e && e₁) = Subst-SuSLik-Expr-1 subst e && Subst-SuSLik-Expr-1 subst e₁
-- Subst-SuSLik-Expr-1 subst (Not e) = Subst-SuSLik-Expr-1 subst e
-- Subst-SuSLik-Expr-1 subst (e == e₁) = Subst-SuSLik-Expr-1 subst e == Subst-SuSLik-Expr-1 subst e₁
-- Subst-SuSLik-Expr-1 subst (Add e e₁) = Add (Subst-SuSLik-Expr-1 subst e) (Subst-SuSLik-Expr-1 subst e₁)

-- Subst-SuSLik-Expr : Subst → SuSLik-Expr → SuSLik-Expr
-- Subst-SuSLik-Expr [] e = e
-- Subst-SuSLik-Expr (x ∷ xs) e = Subst-SuSLik-Expr xs (Subst-SuSLik-Expr-1 x e)

-- Subst-SuSLik-Heaplet : Subst → SuSLik-Heaplet → SuSLik-Heaplet
-- Subst-SuSLik-Heaplet subst (x :-> x₁) = (Subst-Addr subst x) :-> (Subst-SuSLik-Expr subst x₁)
--   -- Intentionally not substituting x, since it is global:
-- Subst-SuSLik-Heaplet subst (x · x₁) = x · Data.List.map (Subst-SuSLik-Expr subst) x₁
-- Subst-SuSLik-Heaplet subst (Temp addr) = Temp (Subst-Addr subst addr)

-- Subst-SuSLik-Heaplets : Subst → List SuSLik-Heaplet → List SuSLik-Heaplet
-- Subst-SuSLik-Heaplets subst hs = Data.List.map (Subst-SuSLik-Heaplet subst) hs

-- Subst-Asn : Subst → SuSLik-Asn → SuSLik-Asn
-- Subst-Asn subst (x ,, x₁) = Subst-SuSLik-Expr subst x ,, Subst-SuSLik-Heaplets subst x₁

-- Addr-fvs : Addr → List Name
-- Addr-fvs (x :+ x₁) = [ x ]
-- Addr-fvs Unused = []

-- Exprs-fvs : List Expr → List Name

-- Expr-fvs : Expr → List Name
-- Expr-fvs (Var x) = [ x ]
-- Expr-fvs (x C· x₁) = Exprs-fvs x₁
-- Expr-fvs (x · e) = Expr-fvs e
-- Expr-fvs (Bool-Lit x) = []
-- Expr-fvs (Int-Lit x) = []
-- Expr-fvs (e && e₁) = Expr-fvs e ++ Expr-fvs e₁
-- Expr-fvs (Not e) = Expr-fvs e
-- Expr-fvs (e == e₁) = Expr-fvs e ++ Expr-fvs e₁
-- Expr-fvs (Add e e₁) = Expr-fvs e ++ Expr-fvs e₁
-- Expr-fvs (Lower x e) = Expr-fvs e
-- Expr-fvs (Instantiate x x₁ x₂ e) = Expr-fvs e
-- Expr-fvs (Lift x) = Addr-fvs x

-- Exprs-fvs [] = []
-- Exprs-fvs (x ∷ xs) = Expr-fvs x ++ Exprs-fvs xs

-- -- data _α=_ : SuSLik-Asn → SuSLik-Asn → Set where
-- --   α=-

-- -- Names-disjoint : List Name → List Name → Set
-- -- Names-disjoint [] _ = ⊤
-- -- Names-disjoint (x ∷ xs) ys = ¬ (x N∈ ys) × Names-disjoint xs ys

-- data Names-disjoint : List Name → List Name → Set where
--   Names-disjoint-Nil : ∀ {ys} → Names-disjoint [] ys
--   Names-disjoint-Cons : ∀ {x xs ys} →
--     ¬ (x N∈ ys) →
--     Names-disjoint xs ys →
--     Names-disjoint (x ∷ xs) ys

-- Subst-⇓ : ∀ {Σ e r v s}
--   (subst : Subst) →
--   Names-disjoint (Data.List.map proj₁ subst) (Expr-fvs e) →
--   Σ ▷ e ⇓[ r , v ] s →
--   Σ ▷ e ⇓[ Subst-Addr subst r , Subst-Name subst v ] (Subst-Asn subst s)
--   -- Σ ▷ (Subst-Expr subst e) ⇓[ Subst-Addr subst r , Subst-Name subst v ] (Subst-Asn subst s)
-- Subst-⇓ subst disjoint ⇓-Var = {!!}
-- Subst-⇓ subst disjoint ⇓-Int = {!!}
-- Subst-⇓ subst disjoint ⇓-Bool = {!!}
-- Subst-⇓ subst disjoint (⇓-Add x x₁ x₂ prf prf₁) = {!!}
-- Subst-⇓ subst disjoint (⇓-Instantiate x prf) = {!!}
-- Subst-⇓ subst disjoint (⇓-Lower-Lower prf) = {!!}
-- Subst-⇓ subst disjoint (⇓-Instantiate-Comp x prf prf₁) = {!!}
-- Subst-⇓ subst disjoint ⇓-Lift = {!!}

-- -- Subst-Name-1-invariant : ∀ {n n′ old new} →
-- --   old ≢ n →
-- --   Subst-Name-1 (old , new) n ≡ n′ →
-- --   n ≡ n′
-- -- Subst-Name-1-invariant {n} {n′} {old} ¬≡ refl with Name-eq-dec {old} {n}
-- -- ... | inj₁ eq = ⊥-elim (¬≡ eq)
-- -- ... | inj₂ y = refl

-- Subst-Name-1-invariant : ∀ {n old new} →
--   old ≢ n →
--   Subst-Name-1 (old , new) n ≡ n
-- Subst-Name-1-invariant {n} {old} ¬≡ with Name-eq-dec {old} {n}
-- ... | inj₁ eq = ⊥-elim (¬≡ eq)
-- ... | inj₂ y = refl

-- Subst-Name-invariant-cons-[] : ∀ {n} {old new} {subst : Subst} →
--   old ≢ n →
--   Subst-Name ((old , new) ∷ []) n ≡ n
-- Subst-Name-invariant-cons-[] {n} {old} {new} {subst} ref with Name-eq-dec {old} {n}
-- ... | inj₁ x = ⊥-elim (ref x)
-- ... | inj₂ y = refl

-- Subst-Name-invariant-cons : ∀ {n n′} {old new} {subst : Subst} →
--   old ≢ n →
--   Subst-Name subst n ≡ n′ →
--   Subst-Name ((old , new) ∷ subst) n ≡ n′
-- Subst-Name-invariant-cons {n} {n′} {old} {new} {[]} ¬≡ prf rewrite prf = Subst-Name-1-invariant ¬≡
-- Subst-Name-invariant-cons {n} {n′} {old} {new} {x ∷ subst₁} ¬≡ prf rewrite prf =
--   let
--     p = Subst-Name-invariant-cons {n} {n′} {old} {new}
--   in
--   Subst-Name-1-invariant {!!}

-- -- Subst-Name-invariant-cons {n} {.(Subst-Name [] n)} {old} {new} {[]} ref refl with Name-eq-dec {Subst-Name-1 (old , new) n} {n}
-- -- ... | inj₁ x = x
-- -- ... | inj₂ y = ⊥-elim (ref {!!})
-- -- Subst-Name-invariant-cons {n} {.(Subst-Name (x ∷ subst₁) n)} {old} {new} {x ∷ subst₁} ref refl = {!!}
-- -- --   with Name-eq-dec (Subst-Name ((old , new) ∷ subst) n) n′
-- -- -- ... | z = ?

-- weaken-¬N∈ : ∀ {n x xs} →
--   ¬ (n N∈ (x ∷ xs)) →
--   ¬ (n N∈ xs)
-- weaken-¬N∈ ref = λ z → ref (there z)

-- weaken-¬N∈-++-1 : ∀ {n xs ys} →
--   ¬ (n N∈ (xs ++ ys)) →
--   ¬ (n N∈ xs)
-- weaken-¬N∈-++-1 = {!!}

-- weaken-¬N∈-++-2 : ∀ {n xs ys} →
--   ¬ (n N∈ (xs ++ ys)) →
--   ¬ (n N∈ ys)
-- weaken-¬N∈-++-2 = {!!}

-- Subst-Name-invariant : ∀ {n} {subst : Subst} →
--   ¬ (n N∈ Data.List.map proj₁ subst) →
--   Subst-Name subst n ≡ n
-- Subst-Name-invariant {n} {[]} ¬∈ = refl
-- Subst-Name-invariant {n} {(x , _) ∷ subst₁} ¬∈ with Name-eq-dec {n} {x}
-- ... | inj₁ eq rewrite eq = ⊥-elim (¬∈ (here Name-N=-≡))
-- ... | inj₂ ¬eq rewrite (Subst-Name-invariant {n} {subst₁} (weaken-¬N∈ ¬∈)) =
--   Subst-Name-1-invariant λ x₁ → ¬eq (sym x₁)

-- Names-disjoint-Var : ∀ {subst : Subst} {n} →
--   Names-disjoint (Data.List.map proj₁ subst) (Expr-fvs (Var n)) →
--   ¬ (n N∈ Data.List.map proj₁ subst)
-- Names-disjoint-Var = {!!}

-- Expr-subst-1-invariant : ∀ {old new e} →
--   ¬ (old N∈ Expr-fvs e) →
--   Subst-Expr-1 (old , new) e ≡ e
-- Expr-subst-1-invariant {old} {new} {Var x} ref = {!!}
-- Expr-subst-1-invariant {old} {new} {x C· x₁} ref = {!!}
-- Expr-subst-1-invariant {old} {new} {x · e} ref rewrite Expr-subst-1-invariant {old} {new} {e} ref = refl
-- Expr-subst-1-invariant {old} {new} {Bool-Lit x} ref = refl
-- Expr-subst-1-invariant {old} {new} {Int-Lit x} ref = refl
-- Expr-subst-1-invariant {old} {new} {e && e₁} ref rewrite Expr-subst-1-invariant {old} {new} {e} (weaken-¬N∈-++-1 ref) | Expr-subst-1-invariant {old} {new} {e₁} (weaken-¬N∈-++-2 ref) = refl
-- Expr-subst-1-invariant {old} {new} {Not e} ref rewrite Expr-subst-1-invariant {old} {new} {e} ref = refl
-- Expr-subst-1-invariant {old} {new} {e == e₁} ref rewrite Expr-subst-1-invariant {old} {new} {e} (weaken-¬N∈-++-1 ref) | Expr-subst-1-invariant {old} {new} {e₁} (weaken-¬N∈-++-2 ref) = refl
-- Expr-subst-1-invariant {old} {new} {Add e e₁} ref rewrite Expr-subst-1-invariant {old} {new} {e} (weaken-¬N∈-++-1 ref) | Expr-subst-1-invariant {old} {new} {e₁} (weaken-¬N∈-++-2 ref) = refl
-- Expr-subst-1-invariant {old} {new} {Lower x e} ref rewrite Expr-subst-1-invariant {old} {new} {e} ref = refl
-- Expr-subst-1-invariant {old} {new} {Instantiate x x₁ x₂ e} ref rewrite Expr-subst-1-invariant {old} {new} {e} ref = refl
-- Expr-subst-1-invariant {old} {new} {Lift x} ref = {!!}

-- Expr-subst-invariant : ∀ {subst e} →
--   Names-disjoint (Data.List.map proj₁ subst) (Expr-fvs e) →
--   Subst-Expr subst e ≡ e
-- -- Expr-subst-invariant {x₁ ∷ subst₁} {Var x} (Names-disjoint-Cons x₂ prf) = {!!}
-- Expr-subst-invariant {[]} {Var x} Names-disjoint-Nil = refl
-- Expr-subst-invariant {(fst , snd) ∷ subst₁} {Var x} (Names-disjoint-Cons x₂ prf) rewrite Expr-subst-invariant {subst₁} {Var x} prf = Expr-subst-1-invariant x₂
-- Expr-subst-invariant {subst} {x C· x₁} prf = {!!}
-- Expr-subst-invariant {subst} {x · e} prf = {!!}
-- Expr-subst-invariant {subst} {Bool-Lit x} prf = {!!}
-- Expr-subst-invariant {subst} {Int-Lit x} prf = {!!}
-- Expr-subst-invariant {subst} {e && e₁} prf = {!!}
-- Expr-subst-invariant {subst} {Not e} prf = {!!}
-- Expr-subst-invariant {subst} {e == e₁} prf = {!!}
-- Expr-subst-invariant {subst} {Add e e₁} prf = {!!}
-- Expr-subst-invariant {subst} {Lower x e} prf = {!!}
-- Expr-subst-invariant {subst} {Instantiate x x₁ x₂ e} prf = {!!}
-- Expr-subst-invariant {subst} {Lift x} prf = {!!}


-- _Sα≡_/_ : SuSLik-Asn → SuSLik-Asn → List Name → Set
-- a Sα≡ b / ns = Σ Subst λ subst → ((Names-disjoint (Data.List.map proj₁ subst) ns) × (a ≡ Subst-Asn subst b))

-- _Eα≡_/_ : Expr → Expr → List Name → Set
-- a Eα≡ b / ns = Σ Subst λ subst → ((Names-disjoint (Data.List.map proj₁ subst) ns) × (a ≡ Subst-Expr subst b))

-- -- Subst-⇓ : ∀ {Σ e r v s} {subst} →
-- --   Σ ▷ e ⇓[ r , v ] s →
-- --   Σ ▷ e ⇓[ r , Subst-Name subst v ] (Subst-Asn subst s)
-- -- Subst-⇓ = ?

-- -- α≡-Expr-invariant : ∀ e

Append-fn : ∀ {A : Set} {xs ys zs : List A} →
  Append xs ys zs →
  zs ≡ xs ++ ys
Append-fn Append-Nil = refl
Append-fn (Append-Cons prf) rewrite Append-fn prf = refl

-- ⇓-Append : ∀ {fr fr₁ fr₁′ fr₂ Σ e r v s s′} →
--   Append fr₁ fr₂ fr →
--   Append fr₁′ fr₂ fr →
--   fr₁ ,, Σ ▷ e ⇓[ r , v ] s →
--   fr₁′ ,, Σ ▷ e ⇓[ r , v ] s′ →
--   fr₁ ≡ fr₁′
-- ⇓-Append prf1 prf2 ⇓-Var ⇓-Var = refl
-- ⇓-Append prf1 prf2 ⇓-Int ⇓-Int = refl
-- ⇓-Append prf1 prf2 ⇓-Bool ⇓-Bool = refl
-- ⇓-Append {fr} {fr₁} {fr₁′} {fr₂} (Append-Cons prf1) (Append-Cons prf2) (⇓-Add x x₁ x₂ x₃ prf3 prf4) (⇓-Add x₄ x₅ x₆ x₇ prf5 prf6) =
--   let
--     p = ⇓-Append prf1 prf2 {!!} {!!}
--   in
--   {!!}
--   -- rewrite (trans (sym (Append-fn prf1)) (Append-fn prf2)) =

--   -- let
--   --   p = Append-fn prf1
--   --   q = Append-fn prf2

--   --   -- r : v₂ ∷ fr ++ fr₂ ≡ v₃ ∷ fr₁ ++ fr₂
--   --   r = trans (sym p) q
--   -- in
--   -- {!!}
-- ⇓-Append prf1 prf2 (⇓-Instantiate x prf3) (⇓-Instantiate x₁ prf4) = {!!}
-- ⇓-Append prf1 prf2 (⇓-Lower-Lower prf3) (⇓-Lower-Lower prf4) = {!!}
-- ⇓-Append prf1 prf2 (⇓-Instantiate-Comp x x₁ prf3 prf4) (⇓-Instantiate-Comp x₂ x₃ prf5 prf6) = {!!}

⇓-Deterministic : ∀ {fr Σ e r v s s′} →
  fr ,, Σ ▷ e ⇓[ r , v ] s →
  fr ,, Σ ▷ e ⇓[ r , v ] s′ →
  s ≡ s′
⇓-Deterministic ⇓-Var ⇓-Var = refl
⇓-Deterministic ⇓-Int ⇓-Int = refl
⇓-Deterministic ⇓-Bool ⇓-Bool = refl
⇓-Deterministic (⇓-Add x x₁ x₂ comb1 comb2 p p₁) (⇓-Add x₅ x₆ x₇ comb3 comb4 q q₁)
  with Combine-Asns-<> comb1 | Combine-Asns-<> comb2 | Combine-Asns-<> comb3 | Combine-Asns-<> comb4
... | refl | refl | refl | refl rewrite ⇓-Deterministic p q | ⇓-Deterministic p₁ q₁ = refl
⇓-Deterministic (⇓-== x x₁ x₂ comb1 comb2 p p₁) (⇓-== x₅ x₆ x₇ comb3 comb4 q q₁)
  with Combine-Asns-<> comb1 | Combine-Asns-<> comb2 | Combine-Asns-<> comb3 | Combine-Asns-<> comb4
... | refl | refl | refl | refl rewrite ⇓-Deterministic p q | ⇓-Deterministic p₁ q₁ = refl

⇓-Deterministic (⇓-Instantiate x comb1 p) (⇓-Instantiate x₂ comb2 q)
  with Combine-Asns-<> comb1 | Combine-Asns-<> comb2
... | refl | refl rewrite ⇓-Deterministic p q = refl

⇓-Deterministic (⇓-Lower-Lower p) (⇓-Lower-Lower q) rewrite ⇓-Deterministic p q = refl
⇓-Deterministic (⇓-Instantiate-Comp x comb1 comb2 p p₁) (⇓-Instantiate-Comp x₃ comb3 comb4 q q₁)
  with Combine-Asns-<> comb1 | Combine-Asns-<> comb2 | Combine-Asns-<> comb3 | Combine-Asns-<> comb4
... | refl | refl | refl | refl rewrite ⇓-Deterministic p q | ⇓-Deterministic p₁ q₁ = refl
⇓-Deterministic ⇓-Lift ⇓-Lift = refl

-- ⇓-Deterministic ⇓-Var ⇓-Var = refl
-- ⇓-Deterministic ⇓-Int ⇓-Int = refl
-- ⇓-Deterministic ⇓-Bool ⇓-Bool = refl
-- ⇓-Deterministic (⇓-Add x x₁ x₂ p p₁) (⇓-Add x₃ x₄ x₅ q q₁) rewrite ⇓-Deterministic p q | ⇓-Deterministic p₁ q₁ = refl
-- ⇓-Deterministic (⇓-Instantiate x p) (⇓-Instantiate x₁ q) rewrite ⇓-Deterministic p q = refl
-- ⇓-Deterministic (⇓-Lower-Lower p) (⇓-Lower-Lower q) rewrite ⇓-Deterministic p q = refl
-- ⇓-Deterministic (⇓-Instantiate-Comp x p p₁) (⇓-Instantiate-Comp x₁ q q₁) rewrite ⇓-Deterministic p q | ⇓-Deterministic p₁ q₁ = refl
-- ⇓-Deterministic ⇓-Lift ⇓-Lift = refl

  -- (fresh : ∀ env → Σ Name λ n → All (_≢ n) env)

-- FS-Names : ∀ fr →
--   Σ (List Name) λ ns →
--   All (λ n → FS-Any (_≡ n) fr) ns
-- FS-Names FS-Empty = [] , []
-- FS-Names (FS-Branch x left right)
-- -- FS-Names (FS-Branch (x ∷ xs) left right) = {!!}
--   with FS-Names left | FS-Names right
-- ... | fst , snd | fst₁ , snd₁ = (x ++ fst ++ fst₁) , {!!}
-- -- ... | fst , snd | fst₁ , snd₁ = (x ++ fst ++ fst₁) , {!!}

-- FS-Names : Fresh-Supply → List Name
-- FS-Names FS-Empty = []
-- FS-Names (FS-Branch xs left right) = xs ++ FS-Names left ++ FS-Names right

data FS-Names : Fresh-Supply → List Name → Set where
  FS-Names-Empty : FS-Names FS-Empty []
  FS-Names-Branch : ∀ {xs ys zs left right appended₀ appended} →
    FS-Names left ys →
    FS-Names right zs →
    Append xs ys appended₀ →
    Append appended₀ zs appended →
    FS-Names (FS-Branch xs left right) appended

→Append : ∀ {A : Set} {xs ys : List A} →
  Append xs ys (xs ++ ys)
→Append {_} {[]} {[]} = Append-Nil
→Append {_} {[]} {x ∷ ys} = Append-Nil
→Append {_} {x ∷ xs} {[]} = Append-Cons →Append
→Append {_} {x ∷ xs} {x₁ ∷ ys} = Append-Cons →Append

++-[] : ∀ {A : Set} {xs : List A} →
  xs ++ [] ≡ xs
++-[] {_} {[]} = refl
++-[] {_} {x ∷ xs} rewrite ++-[] {_} {xs} = refl

++-assoc : ∀ {A : Set} {xs ys zs : List A} →
  xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
++-assoc {_} {[]} {[]} {[]} = refl
++-assoc {_} {[]} {[]} {x ∷ zs} = refl
++-assoc {_} {[]} {x ∷ ys} {[]} = refl
++-assoc {_} {[]} {x ∷ ys} {x₁ ∷ zs} = refl
++-assoc {_} {x ∷ xs} {[]} {[]} rewrite ++-assoc {_} {xs} {[]} {[]} | ++-[] {_} {xs} | ++-[] {_} {xs} | ++-[] {_} {xs} = refl
++-assoc {_} {x ∷ xs} {[]} {x₁ ∷ zs} rewrite ++-[] {_} {xs} = refl
++-assoc {_} {x ∷ xs} {x₁ ∷ ys} {[]} rewrite ++-[] {_} {xs ++ x₁ ∷ ys} | ++-assoc {_} {xs} {x₁ ∷ ys} {[]} | ++-[] {_} {x ∷ (xs ++ x₁ ∷ ys)} = refl
++-assoc {_} {x ∷ xs} {x₁ ∷ ys} {x₂ ∷ zs} rewrite ++-assoc {_} {xs} {x₁ ∷ ys} {x₂ ∷ zs} = refl

-- Append (x ++ fst) fst₁ (x ++ fst ++ fst₁)

FS-Names-exists : ∀ fr →
  Σ (List Name) λ names →
    FS-Names fr names
FS-Names-exists FS-Empty = [] , FS-Names-Empty
FS-Names-exists (FS-Branch x left right) with FS-Names-exists left | FS-Names-exists right
... | fst , snd | fst₁ , snd₁ = (x ++ fst ++ fst₁) , FS-Names-Branch snd snd₁ →Append (subst (λ x₁ → Append (x ++ fst) fst₁ x₁) (sym (++-assoc {_} {x} {fst} {fst₁})) →Append)

Append-cons-eq : ∀ {A : Set} {x x′ : A} {xs ys zs} →
  Append (x ∷ xs) ys (x′ ∷ zs) →
  x ≡ x′
Append-cons-eq (Append-Cons prf) = refl

-- FS-Names-not-head : ∀ {fr x xs} →
--   FS-Names fr 

dec-∈ : ∀ {x : Name} {xs} →
  (Any (_≡ x) xs) ⊎ (All (_≢ x) xs)
dec-∈ {x} {[]} = inj₂ []
dec-∈ {x} {x₁ ∷ xs} with Name-eq-dec {x} {x₁}
... | inj₁ refl = inj₁ (here refl)
... | inj₂ p with dec-∈ {x} {xs}
dec-∈ {x} {x₁ ∷ xs} | inj₂ p | inj₁ x₂ = inj₁ (there x₂)
dec-∈ {x} {x₁ ∷ xs} | inj₂ p | inj₂ y = inj₂ ((λ x₂ → p (sym x₂)) ∷ y)

Append-right : ∀ {n : Name} {xs ys zs} →
  All (_≢ n) xs →
  Any (_≡ n) zs →
  Append xs ys zs →
  Any (_≡ n) ys
Append-right [] (here px) Append-Nil = here px
Append-right [] (there prf2) Append-Nil = there prf2
Append-right (px ∷ prf1) (here px₁) (Append-Cons prf3) = ⊥-elim (px px₁)
Append-right (px ∷ prf1) (there prf2) (Append-Cons prf3) = Append-right prf1 prf2 prf3

Append-trans : ∀ {A : Set} {a b c d e : List A} →
  Append a b c →
  Append c d e →
  e ≡ (a ++ b) ++ d
Append-trans prf1 prf2 rewrite sym (Append-fn prf1) | (Append-fn prf2) = refl

Append-¬in-either : ∀ {x : Name} {xs ys zs} →
  All (_≢ x) xs →
  All (_≢ x) ys →
  Append xs ys zs →
  All (_≢ x) zs
Append-¬in-either [] [] append rewrite (Append-fn append) = []
Append-¬in-either [] (px ∷ prf2) append rewrite (Append-fn append) = px ∷ prf2
Append-¬in-either (px ∷ prf1) prf2 (Append-Cons append) = px ∷ Append-¬in-either prf1 prf2 append

¬All-Any : ∀ {xs} (P : Name → Set) →
  All (λ x → ¬ P x) xs →
  Any P xs →
  ⊥
¬All-Any P [] = λ ()
¬All-Any P (px ∷ prf) (here px₁) = px px₁
¬All-Any P (px ∷ prf) (there prf2) = ¬All-Any P prf prf2

⊆-FS-Names : ∀ {fr n names} →
  FS-Names fr names →
  Any (_≡ n) names →
  FS-Any (_≡ n) fr
⊆-FS-Names {(FS-Branch [] _ right)} {n} {x ∷ names} (FS-Names-Branch {[]} {[]} {zs} prf1 prf2 x₁ x₂) (here px) rewrite (sym (Append-++ x₁)) | (Append-++ x₂) =
  FS-Right (⊆-FS-Names {_} {n} prf2 (here px))

⊆-FS-Names {(FS-Branch [] _ _)} {n} {x ∷ names} (FS-Names-Branch {[]} {x₃ ∷ ys} {zs} prf1 prf2 x₁ x₂) (here px) rewrite (sym (Append-++ x₁)) | Append-cons-eq x₂ =
  FS-Left (⊆-FS-Names {_} {n} prf1 (here px))

⊆-FS-Names {(FS-Branch (x₃ ∷ xs) _ _)} {n} {x ∷ names} (FS-Names-Branch {x₃ ∷ xs} prf1 prf2 x₁ x₂) (here px) rewrite (sym (Append-++ x₁)) | Append-cons-eq x₂ = FS-Here (here px)

⊆-FS-Names {FS-Branch [] _ _} {n} {x ∷ names} (FS-Names-Branch {.[]} {[]} {zs} prf1 prf2 x₁ x₂) (there prf3) rewrite (sym (Append-++ x₁)) | sym (Append-fn x₂) =
  FS-Right (⊆-FS-Names {_} {n} prf2 (there prf3))

⊆-FS-Names {FS-Branch [] _ _} {n} {x ∷ names} (FS-Names-Branch {.[]} {x₃ ∷ ys} {zs} prf1 prf2 x₁ x₂) (there prf3)
  with dec-∈ {n} {x₃ ∷ ys}
... | inj₁ x₄ = FS-Left (⊆-FS-Names prf1 x₄)
... | inj₂ y rewrite (Append-fn x₁) = FS-Right (⊆-FS-Names prf2 (Append-right y (there prf3) x₂))

⊆-FS-Names {FS-Branch (x₃ ∷ xs) _ _} {n} {x ∷ names} (FS-Names-Branch {.(x₃ ∷ xs)} {ys} {zs} prf1 prf2 x₁ x₂) (there prf3)
  with dec-∈ {n} {x₃ ∷ xs}
... | inj₁ x₄ = FS-Here x₄
... | inj₂ y with dec-∈ {n} {ys}
⊆-FS-Names {FS-Branch (x₃ ∷ xs) _ _} {n} {x ∷ names} (FS-Names-Branch {.(x₃ ∷ xs)} {ys} {zs} prf1 prf2 x₁ x₂) (there prf3) | inj₂ y | inj₁ p = FS-Left (⊆-FS-Names prf1 p)
⊆-FS-Names {FS-Branch (x₃ ∷ xs) _ _} {n} {x ∷ names} (FS-Names-Branch {.(x₃ ∷ xs)} {ys} {zs} prf1 prf2 x₁ x₂) (there prf3) | inj₂ y | inj₂ q with dec-∈ {n} {zs}
⊆-FS-Names {FS-Branch (x₃ ∷ xs) _ _} {n} {x ∷ names} (FS-Names-Branch {.(x₃ ∷ xs)} {ys} {zs} prf1 prf2 x₁ x₂) (there prf3) | inj₂ y | inj₂ q | inj₁ r = FS-Right (⊆-FS-Names prf2 r)
⊆-FS-Names {FS-Branch (x₃ ∷ xs) _ _} {n} {x ∷ names} (FS-Names-Branch {.(x₃ ∷ xs)} {ys} {zs} {left} {right} {appended₀} prf1 prf2 x₁ x₂) (there prf3) | inj₂ y | inj₂ q | inj₂ s =
  let w = Append-¬in-either {n} y q x₁
      w′ = Append-¬in-either {n} w s x₂
  in
  ⊥-elim (¬All-Any (_≡ n) w′ (there prf3))

Append-left-[] : ∀ {A : Set} {xs ys : List A} →
  Append xs ys [] →
  xs ≡ []
Append-left-[] Append-Nil = refl

Append-right-[] : ∀ {A : Set} {xs ys : List A} →
  Append xs ys [] →
  ys ≡ []
Append-right-[] Append-Nil = refl

¬Append-left-cons-nil : ∀ {A : Set} {x : A} {xs ys} → Append (x ∷ xs) ys [] → ⊥
¬Append-left-cons-nil ()

¬FS-Any-[] : ∀ {P} {fr} → FS-Names fr [] → FS-Any P fr → ⊥
¬FS-Any-[] (FS-Names-Branch fs-names fs-names₁ x x₁) (FS-Here (here px)) rewrite Append-left-[] x₁ | Append-right-[] x | Append-left-[] x = ¬Append-left-cons-nil x
¬FS-Any-[] (FS-Names-Branch fs-names fs-names₁ x x₁) (FS-Here (there x₂)) rewrite Append-left-[] x₁ = ¬Append-left-cons-nil x
¬FS-Any-[] (FS-Names-Branch fs-names fs-names₁ x x₁) (FS-Left prf) rewrite Append-left-[] x₁ | Append-right-[] x = ¬FS-Any-[] fs-names prf
¬FS-Any-[] (FS-Names-Branch fs-names fs-names₁ x x₁) (FS-Right prf) rewrite Append-right-[] x₁ = ¬FS-Any-[] fs-names₁ prf

Any-++ : ∀ {A : Set} {P : A → Set} {xs ys zs} →
  Any P xs →
  Any P ((xs ++ ys) ++ zs)
Any-++ (here px) = here px
Any-++ (there prf) = there (Any-++ prf)

Any-++-2 : ∀ {A : Set} {P : A → Set} {xs ys zs} →
  Any P ys →
  Any P ((xs ++ ys) ++ zs)
Any-++-2 {_} {_} {[]} (here px) = here px
Any-++-2 {_} {_} {[]} (there prf) = there (Any-++-2 {_} {_} {[]} {_} {_} prf)
Any-++-2 {_} {_} {x ∷ xs} {ys} {zs} prf = there (Any-++-2 {_} {_} {xs} {ys} {zs} prf)

Any-++-right : ∀ {A : Set} {P : A → Set} {xs ys} →
  Any P ys →
  Any P (xs ++ ys)
Any-++-right {_} {_} {[]} {ys} prf = prf
Any-++-right {_} {_} {x ∷ xs} {ys} prf = there (Any-++-right prf)

FS-Names-⊆ : ∀ {fr n names} →
  FS-Names fr names →
  FS-Any (_≡ n) fr →
  Any (_≡ n) names
FS-Names-⊆ {fr} {n} {[]} prf1 prf2 = ⊥-elim (¬FS-Any-[] prf1 prf2)
FS-Names-⊆ {.(FS-Branch _ _ _)} {n} {x ∷ names} (FS-Names-Branch prf1 prf2 x₁ x₂) (FS-Here x₃) rewrite (Append-fn x₂) | (Append-fn x₁) = Any-++ x₃
FS-Names-⊆ {.(FS-Branch _ _ _)} {n} {x ∷ names} (FS-Names-Branch {xs} {ys} {zs} prf1 prf2 x₁ x₂) (FS-Left prf3) rewrite (Append-fn x₂) | (Append-fn x₁) = Any-++-2 {_} {_} {xs} {ys} {zs} (FS-Names-⊆ prf1 prf3)
FS-Names-⊆ {.(FS-Branch _ _ _)} {n} {x ∷ names} (FS-Names-Branch {xs} {ys} {zs} prf1 prf2 x₁ x₂) (FS-Right prf3) rewrite (Append-fn x₂) | (Append-fn x₁) = Any-++-right (FS-Names-⊆ prf2 prf3)

FS-fresh : ∀ fr →
  Σ Name λ n →
    ¬ FS-Any (_≡ n) fr
FS-fresh fr =
  let
    fs-names = FS-Names-exists fr
    n , prf = fresh (proj₁ fs-names)
  in
  n , λ x →
    let
      p = FS-Names-⊆ (proj₂ fs-names) x
    in
    ¬All-Any (_≡ n) prf p

-- ¬FS-Any⇒FS-All : ∀ fr


-- FS-fresh : ∀ fr →
--   Σ Name λ n →
--     FS-All (_≢ n) fr
-- FS-fresh fr =
--   let
--     fs-names = FS-Names-exists fr
--     n , prf = fresh (proj₁ fs-names)
--     -- p = ⊆-FS-Names (proj₂ fs-names) {!!}
--   in
--   n , {!!}

-- FS-fresh FS-Empty = proj₁ (fresh []) , FS-All-Empty
-- FS-fresh (FS-Branch x fr fr₁) = proj₁ (FS-fresh fr₁) , FS-All-Branch {!!} {!!} {!!}

fresh-first : ∀ {x xs} →
  proj₁ (fresh (x ∷ xs)) ≢ x
fresh-first {x} {xs} with proj₂ (fresh (x ∷ xs))
... | px ∷ z = λ eq → px (sym eq)

fresh-second : ∀ {x y rest} →
  proj₁ (fresh (x ∷ y ∷ rest)) ≢ y
fresh-second {x} {y} {rest} with proj₂ (fresh (x ∷ y ∷ rest))
... | _ ∷ py ∷ z = λ eq → py (sym eq)


⇓-Total : ∀ {env e r v} →
  Σ Fresh-Supply λ fr →
  Σ SuSLik-Asn λ s →
    fr ,, env ▷ e ⇓[ r , v ] s
⇓-Total {env} {Var x} {r} {v} = FS-Empty , ((Var v == Var x) ,, ((r :-> Var v) ∷ [])) , ⇓-Var
⇓-Total {env} {x C· x₁} {r} {v} = {!!}
⇓-Total {env} {x · e} {r} {v} = {!!}
⇓-Total {env} {Bool-Lit x} {r} {v} = FS-Empty , ((Var v == Bool-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Bool
⇓-Total {env} {Int-Lit x} {r} {v} = FS-Empty , ((Var v == Int-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Int
-- ⇓-Total {env} {e && e₁} {r} {v} =
--   let v₁ , v₁-prf = fresh []
--       v₂ , v₂-prf = fresh [ v₁ ]
--   in
--   {!!} , ({!!} ,, {!!}) , {!⇓-And!}
  -- proj₁ ⇓-Total , ((Var v ,, []) , {!!})
-- ⇓-Total {env} {Not e} {r} {v} = proj₁ ⇓-Total , ((Var v ,, []) , {!!})
-- ⇓-Total {env} {Not e} {r} {v} = {!!} , {!!} , {!⇓-Not!}
⇓-Total {env} {e == e₁} {r} {v} =
  let v₁ , v₁-prf = fresh [ v ]
      v₂ , v₂-prf = fresh (v ∷ v₁ ∷ [])

      left = ⇓-Total {env} {e} {Unused-Addr} {v₁}
      right = ⇓-Total {env} {e₁} {Unused-Addr} {v₂}

      s₁ = proj₁ (proj₂ left)
      s₂ = proj₁ (proj₂ right)

      asn = ((Var v == ((Var v₁) == (Var v₂))) ,, []) <> s₁ <> s₂
  in
  FS-Branch (v₁ ∷ v₂ ∷ []) (proj₁ left) (proj₁ right) , asn , ⇓-== fresh-first fresh-first fresh-second Combine-Asns-exists Combine-Asns-exists (proj₂ (proj₂ left)) (proj₂ (proj₂ right))
⇓-Total {env} {Add e e₁} {r} {v} = {!!}
⇓-Total {env} {Lower x e} {r} {v} = {!!}
⇓-Total {env} {Instantiate x x₁ x₂ e} {r} {v} = {!!}
⇓-Total {env} {Lift x} {r} {v} = FS-Empty ,
                                   (((Var v == Addr-Var r) && (Addr-Var r == Addr-Var x)) ,, []) ,
                                   ⇓-Lift

-- ⇓-Total {env} {Var x} {r} {v} = FS-Empty , ((Var v == Var x) ,, ((r :-> Var v) ∷ [])) , ⇓-Var
-- ⇓-Total {env} {x C· x₁} {r} {v} = {!!}
-- ⇓-Total {env} {x · e} {r} {v} = {!!}
-- ⇓-Total {env} {Bool-Lit x} {r} {v} = FS-Empty , ((Var v == Bool-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Bool
-- ⇓-Total {env} {Int-Lit x} {r} {v} = FS-Empty , ((Var v == Int-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Int
-- ⇓-Total {env} {e && e₁} {r} {v} = proj₁ ⇓-Total , ((Var v ,, []) , {!!})
-- ⇓-Total {env} {Not e} {r} {v} = proj₁ ⇓-Total , ((Var v ,, []) , {!⇓-Not!})
-- ⇓-Total {env} {e == e₁} {r} {v} = {!!}
-- ⇓-Total {env} {Add e e₁} {r} {v} = {!!}
-- ⇓-Total {env} {Lower x e} {r} {v} = {!!}
-- ⇓-Total {env} {Instantiate x x₁ x₂ e} {r} {v} = {!!}
-- ⇓-Total {env} {Lift x} {r} {v} = FS-Empty ,
--                                    (((Var v == Addr-Var r) && (Addr-Var r == Addr-Var x)) ,, []) ,
--                                    ⇓-Lift

S[_,_]⟦_⟧_ : Addr → Name → Expr → G-Env → SuSLik-Asn
S[ r , v ]⟦ e ⟧ env with ⇓-Total {env} {e} {r} {v}
... | fst , fst₁ , snd = fst₁



-- ⇓-Deterministic ⇓-Var ⇓-Var = refl
-- ⇓-Deterministic ⇓-Int ⇓-Int = refl
-- ⇓-Deterministic ⇓-Bool ⇓-Bool = refl
-- ⇓-Deterministic (⇓-Add {fr} {fr₁} {fr₂} app₁ x₁ x₂ x₃ p p₁) (⇓-Add {fr′} {fr₁′} {fr₂′} app₂ x₅ x₆ x₇ q q₁) rewrite Append-fn app₁ | Append-fn app₂
--   with ⇓-Deterministic p q
-- ... | z = ?
-- ⇓-Deterministic (⇓-Instantiate x p) (⇓-Instantiate x₁ q) = {!!}
-- ⇓-Deterministic (⇓-Lower-Lower p) (⇓-Lower-Lower q) = {!!}
-- ⇓-Deterministic (⇓-Instantiate-Comp x x₁ p p₁) (⇓-Instantiate-Comp x₂ x₃ q q₁) = {!!}

-- ⇓-Deterministic ⇓-Int ⇓-Int = [] , (Names-disjoint-Nil , refl)
-- ⇓-Deterministic ⇓-Bool ⇓-Bool = [] , (Names-disjoint-Nil , refl)
-- -- Σ ▷ e₁ ⇓[ Unused-Addr , v₁ ] _s′_774
-- ⇓-Deterministic {Σ} {e} {r} {v} {s} {s′} (⇓-Add {_} {e₁} {_} {_} {_} {v₀} {v₁} x x₁ x₂ prf₁ prf₂) (⇓-Add {_} {e₂} {_} {_} {_} {v₀′} {v₁′} {s₁′} x₃ x₄ x₅ prf₃ prf₄)
--   with ⇓-Deterministic prf₁ (subst (λ x₆ → Σ ▷ e₂ ⇓[ Unused-Addr , v₀ ] x₆) {!!} (subst (λ x₇ → Σ ▷ e₂ ⇓[ Unused-Addr , x₇ ] s₁′) {!!} prf₃))
-- ... | z = {!!}
-- ⇓-Deterministic (⇓-Instantiate x prf₁) (⇓-Instantiate x₁ prf₂) = {!!}
-- ⇓-Deterministic (⇓-Lower-Lower prf₁) (⇓-Lower-Lower prf₂) = {!!}
-- ⇓-Deterministic (⇓-Instantiate-Comp x prf₁ prf₂) (⇓-Instantiate-Comp x₁ prf₃ prf₄) = {!!}
-- ⇓-Deterministic ⇓-Lift ⇓-Lift = [] , (Names-disjoint-Nil , refl)

-- -- Type checking --
-- -- data _⊢_▷_⇒_ : Env → G-Env → Expr → Type → Set where
-- --   ⇒-Var-Layout : ∀ {Γ} {Σ} {n : Name} {e : Expr} {A} →
-- --     Env-lookup n Γ (e , Layout-Type A) →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ Var n ⇒ Layout-Type A

-- --   ⇒-Var-Base-Type : ∀ {Γ} {Σ} {n : Name} {e : Expr} {τ} →
-- --     Env-lookup n Γ (e , τ) →
-- --     Base-Type τ →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ Var n ⇒ τ

-- --   ⇒-Bool-Lit : ∀ {Γ Σ b} →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ Bool-Lit b ⇒ Bool-Type

-- --   ⇒-Int-Lit : ∀ {Γ Σ i} →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ Int-Lit i ⇒ Int-Type

-- --   ⇒-&& : ∀ {Γ Σ x y} →
-- --     Γ ⊢ Σ ▷ x ⇒ Bool-Type →
-- --     Γ ⊢ Σ ▷ y ⇒ Bool-Type →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ (x && y) ⇒ Bool-Type

-- --   ⇒-Not : ∀ {Γ Σ x} →
-- --     Γ ⊢ Σ ▷ x ⇒ Bool-Type →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ Not x ⇒ Bool-Type

-- --   ⇒-== : ∀ {Γ Σ x y} →
-- --     Γ ⊢ Σ ▷ x ⇒ Int-Type →
-- --     Γ ⊢ Σ ▷ y ⇒ Int-Type →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ (x == y) ⇒ Bool-Type

-- --   ⇒-Add : ∀ {Γ Σ x y} →
-- --     Γ ⊢ Σ ▷ x ⇒ Int-Type →
-- --     Γ ⊢ Σ ▷ y ⇒ Int-Type →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ (Add x y) ⇒ Int-Type

-- --   ⇒-Mul : ∀ {Γ Σ x y} →
-- --     Γ ⊢ Σ ▷ x ⇒ Int-Type →
-- --     Γ ⊢ Σ ▷ y ⇒ Int-Type →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ (Mul x y) ⇒ Int-Type

-- --   ⇒-App : ∀ {Γ Σ α B d f e} →
-- --     G-Env-lookup f Σ (d , α ⟶ Layout-Type B) →
-- --     Γ ⊢ Σ ▷ e ⇒ α →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ (f · e) ⇒ Layout-Type B

-- --   ⇒-Lower : ∀ {Γ Σ A e d τ} →
-- --     G-Env-lookup A Σ (d , τ ⟶ Layout-Type A) →  -- A is a layout for τ
-- --     ---------------
-- --     Γ ⊢ Σ ▷ Lower A e ⇒ Layout-Type A

-- --   ⇒-Instantiate : ∀ {Γ Σ A B α β f d-f d-A d-B} →
-- --     G-Env-lookup A Σ (d-A , α ⟶ Layout-Type A) → -- A is a layout for α
-- --     G-Env-lookup B Σ (d-B , β ⟶ Layout-Type B) → -- B is a layout for β
-- --     G-Env-lookup f Σ (d-f , α ⟶ β) →
-- --     ---------------
-- --     Γ ⊢ Σ ▷ Instantiate A B f ⇒ (Layout-Type A ⟶ Layout-Type B)

-- -- Concrete : Env → G-Env → Expr → Set
-- -- Concrete Γ Σ e = ∃[ τ ](Γ ⊢ Σ ▷ e ⇒ τ)

-- -- -- -- Translate an expression of base type
-- -- -- data _⟶base_ : Expr → SuSLik-Expr → Set where
-- -- --   ⟶base-Var : ∀ {Γ }

-- -- -- Layout translation --

-- -- -- data _⟶heaplet_ : Heaplet → SuSLik-Heaplet → Set where
-- -- --   ⟶heaplet-:-> : ∀ {a e} →

