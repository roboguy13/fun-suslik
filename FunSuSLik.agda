open import Data.Sum
open import Data.Product
open import Data.List
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Unary.Any
open import Data.Nat
open import Data.Bool
open import Data.Integer

open ≡-Reasoning

module FunSuSLik
  (Global-Name : Set)
  (Global-Name-eq-dec : ∀ {a b : Global-Name} → (a ≡ b) ⊎ (a ≢ b))
  where

-- TODO: Might be better to use strings
data Name : Set where
  Mk-Name : ℕ → Name

data Params : Set where
  Mk-Params : ℕ → Params

Valid-Param : Name → Params → Set
Valid-Param (Mk-Name n) (Mk-Params p) = n Data.Nat.< p

-- Name : Set
-- Name = ℕ

-- fun-SuSLik Language
data Type : Set where
  Int-Type : Type
  Bool-Type : Type
  _⟶_ : Type → Type → Type
  Adt-Type : Global-Name → Type
  Layout-Type : Global-Name → Type

data Expr : Set where
  Var : Name → Expr
  _C·_ : Global-Name → List Expr → Expr
  _·_ : Global-Name → Expr → Expr

  Bool-Lit : Bool → Expr
  Int-Lit : ℤ → Expr

  _&&_ : Expr → Expr → Expr
  Not : Expr → Expr

  _==_ : Expr → Expr → Expr

  Add : Expr → Expr → Expr
  Mul : Expr → Expr → Expr

  Lower : Global-Name → Expr → Expr
  Instantiate :
    Global-Name → -- Input layout
    Global-Name → -- Output layout
    Global-Name → -- Function name
    Expr

data Guard-Branch : Set where
  Mk-Guard-Branch :
    Expr → -- Boolean guard
    Expr → -- RHS
    Guard-Branch

data Fn-Branch : Set where
  Mk-Fn-Branch :
    Global-Name →       -- Constructor name
    Params →            -- Pattern variables
    List Guard-Branch → -- Guarded RHS's
    Fn-Branch


data Fn-Def : Set where
  Mk-Fn-Def : List Fn-Branch → Fn-Def

data Addr : Set where
  [_+_] : Name → ℕ → Addr

data Heaplet : Set where
  _:->_ : Addr → Expr → Heaplet
  _H·_ : Global-Name → Expr → Heaplet

data Layout-Branch : Set where
  Mk-Layout-Branch :
    Global-Name →  -- Constructor name
    Params →       -- Formal parameters
    List Heaplet → -- Body
    Layout-Branch

data Layout : Set where
  Mk-Layout : List Layout-Branch → Layout


-- SuSLik Language
data SuSLik-Expr : Set where
  Var : Name → SuSLik-Expr

  Bool-Lit : Bool → SuSLik-Expr
  Int-Lit : ℤ → SuSLik-Expr

  _&&_ : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr
  Not : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr

  _==_ : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr

  Add : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr
  Mul : SuSLik-Expr → SuSLik-Expr → SuSLik-Expr

data SuSLik-Heaplet : Set where
  _:->_ : Addr → SuSLik-Expr → SuSLik-Heaplet
  _·_ : Global-Name → List Name → SuSLik-Heaplet


data SuSLik-Ind-Branch : Set where
  Mk-SuSLik-Ind-Branch :
    SuSLik-Expr →    -- Condition
    SuSLik-Heaplet → -- RHS
    SuSLik-Ind-Branch

data SuSLik-Ind : Set where
  Mk-SuSLik-Ind :
    Params →
    List SuSLik-Ind-Branch →
    SuSLik-Ind

data Global-Def : Set where
  Global-Fn : Fn-Def → Global-Def
  Global-Layout : Layout → Global-Def

-- Global environment
G-Env : Set
G-Env = List (Global-Name × Global-Def × Type)

Env : Set
Env = List (Expr × Type)

SuSLik-Env : Set
SuSLik-Env = List SuSLik-Expr

data Env-lookup : Name → Env → (Expr × Type) → Set where
  Env-here : ∀ {x xs} → Env-lookup (Mk-Name 0) (x ∷ xs) x
  Env-there : ∀ {n x xs e} →
    Env-lookup (Mk-Name n) xs e →
    Env-lookup (Mk-Name (ℕ.suc n)) (x ∷ xs) e

data G-Env-lookup : Global-Name → G-Env → (Global-Def × Type) → Set where
  G-Env-here : ∀ {n xs d} → G-Env-lookup n ((n , d) ∷ xs) d
  G-Env-there : ∀ {n x xs d} →
    G-Env-lookup n xs d →
    G-Env-lookup n (x ∷ xs) d

data Base-Type : Type → Set where
  Base-Type-Int : Base-Type Int-Type
  Base-Type-Bool : Base-Type Bool-Type

-- Type checking --
data _⊢_▷_⇒_ : Env → G-Env → Expr → Type → Set where
  ⇒-Var-Layout : ∀ {Γ} {Σ} {n : Name} {e : Expr} {A} →
    Env-lookup n Γ (e , Layout-Type A) →
    ---------------
    Γ ⊢ Σ ▷ Var n ⇒ Layout-Type A

  ⇒-Var-Base-Type : ∀ {Γ} {Σ} {n : Name} {e : Expr} {τ} →
    Env-lookup n Γ (e , τ) →
    Base-Type τ →
    ---------------
    Γ ⊢ Σ ▷ Var n ⇒ τ

  ⇒-Bool-Lit : ∀ {Γ Σ b} →
    ---------------
    Γ ⊢ Σ ▷ Bool-Lit b ⇒ Bool-Type

  ⇒-Int-Lit : ∀ {Γ Σ i} →
    ---------------
    Γ ⊢ Σ ▷ Int-Lit i ⇒ Int-Type

  ⇒-&& : ∀ {Γ Σ x y} →
    Γ ⊢ Σ ▷ x ⇒ Bool-Type →
    Γ ⊢ Σ ▷ y ⇒ Bool-Type →
    ---------------
    Γ ⊢ Σ ▷ (x && y) ⇒ Bool-Type

  ⇒-Not : ∀ {Γ Σ x} →
    Γ ⊢ Σ ▷ x ⇒ Bool-Type →
    ---------------
    Γ ⊢ Σ ▷ Not x ⇒ Bool-Type

  ⇒-== : ∀ {Γ Σ x y} →
    Γ ⊢ Σ ▷ x ⇒ Int-Type →
    Γ ⊢ Σ ▷ y ⇒ Int-Type →
    ---------------
    Γ ⊢ Σ ▷ (x == y) ⇒ Bool-Type

  ⇒-Add : ∀ {Γ Σ x y} →
    Γ ⊢ Σ ▷ x ⇒ Int-Type →
    Γ ⊢ Σ ▷ y ⇒ Int-Type →
    ---------------
    Γ ⊢ Σ ▷ (Add x y) ⇒ Int-Type

  ⇒-Mul : ∀ {Γ Σ x y} →
    Γ ⊢ Σ ▷ x ⇒ Int-Type →
    Γ ⊢ Σ ▷ y ⇒ Int-Type →
    ---------------
    Γ ⊢ Σ ▷ (Mul x y) ⇒ Int-Type

  ⇒-App : ∀ {Γ Σ α B d f e} →
    G-Env-lookup f Σ (d , α ⟶ Layout-Type B) →
    Γ ⊢ Σ ▷ e ⇒ α →
    ---------------
    Γ ⊢ Σ ▷ (f · e) ⇒ Layout-Type B

  ⇒-Lower : ∀ {Γ Σ A e d τ} →
    G-Env-lookup A Σ (d , τ ⟶ Layout-Type A) →  -- A is a layout for τ
    ---------------
    Γ ⊢ Σ ▷ Lower A e ⇒ Layout-Type A

  ⇒-Instantiate : ∀ {Γ Σ A B α β f d-f d-A d-B} →
    G-Env-lookup A Σ (d-A , α ⟶ Layout-Type A) → -- A is a layout for α
    G-Env-lookup B Σ (d-B , β ⟶ Layout-Type B) → -- B is a layout for β
    G-Env-lookup f Σ (d-f , α ⟶ β) →
    ---------------
    Γ ⊢ Σ ▷ Instantiate A B f ⇒ (Layout-Type A ⟶ Layout-Type B)

Concrete : Env → G-Env → Expr → Set
Concrete Γ Σ e = ∃[ τ ](Γ ⊢ Σ ▷ e ⇒ τ)

-- Translate an expression of base type
data _⟶base_ : Expr → SuSLik-Expr → Set where
  ⟶base-Var : ∀ {Γ }

-- Layout translation --

-- data _⟶heaplet_ : Heaplet → SuSLik-Heaplet → Set where
--   ⟶heaplet-:-> : ∀ {a e} →

