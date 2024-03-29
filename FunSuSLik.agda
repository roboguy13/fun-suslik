open import Data.Sum
open import Data.Product
open import Data.List
open import Data.Maybe
open import Data.Unit
open import Data.Empty
open import Relation.Nullary
open import Relation.Nullary.Decidable
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

_∈_ : {A : Set} → A → List A → Set
x ∈ xs = Any (_≡ x) xs


Name-N=-≡ : ∀ {a : Name} → a N= a
Name-N=-≡ {a} with Name-eq-dec {a} {a}
... | inj₁ x = tt
... | inj₂ y = y refl

data Addr : Set where
  _:+_ : Name → ℕ → Addr
  Unused-Addr : Addr -- TODO: Figure this out in more detail

data Expr : Set

data Heaplet : Set where
  _:->_ : Addr → Name → Heaplet
  _H·_ : Name → Name → Heaplet
  -- _:->_ : Addr → Expr → Heaplet
  -- _H·_ : Name → Expr → Heaplet


data Layout-Branch : Set where
  Mk-Layout-Branch :
    Name →         -- Constructor name
    -- Params →       -- Formal parameters
    List Heaplet → -- Body
    Layout-Branch

data Layout : Set where
  Mk-Layout :
    Name → -- Layout name
    (Name × Name) → -- The type, consisting of: the ADT name and the list of SuSLik parameters
    List Layout-Branch →
    Layout

-- fun-SuSLik Language
data Type : Set where
  Int-Type : Type
  Bool-Type : Type
  _⟶_ : Type → Type → Type
  Adt-Type : Name → Type
  Layout-Type : Name → Type
  -- _>->_ : Name → Name → Type

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

  Lower : Name → Expr → Expr
  Instantiate :
    Name → -- Input layout
    Name → -- Output layout
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
  Mk-Fn-Def : Type → Type → List Fn-Branch → Fn-Def

Fn-Def-Type : Fn-Def → Type
Fn-Def-Type (Mk-Fn-Def τ₁ τ₂ _) = τ₁ ⟶ τ₂

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

→SuSLik-Heaplet-fn : Heaplet → SuSLik-Heaplet
→SuSLik-Heaplet-fn (x :-> x₁) = x :-> Var x₁
→SuSLik-Heaplet-fn (x H· x₁) = x · [ Var x₁ ]

data →SuSLik-Heaplet : Heaplet → SuSLik-Heaplet → Set where
  →SuSLik-Heaplet-points-to : ∀ {x y} →
    →SuSLik-Heaplet (x :-> y) (x :-> Var y)

  →SuSLik-Heaplet-H· : ∀ {p arg} →
    →SuSLik-Heaplet (p H· arg) (p · [ Var arg ])

data SuSLik-Asn : Set where
  _,,_ :
    SuSLik-Expr → -- Pure part
    List SuSLik-Heaplet → -- Spatial part
    SuSLik-Asn

-- Generate SuSLik inductive predicate names for instantiated functions
postulate
  I : Name → Name → Name → Name
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

Ty-Env : Set
Ty-Env = List (Name × Type)

data Adt-Branch : Set where
  Mk-Adt-Branch :
    Name →      -- Constructor name
    List Type → -- Field types
    Adt-Branch

data Adt : Set where
  Mk-Adt : List Adt-Branch → Adt

data Global-Def : Set where
  G-Fn-Def : Fn-Def → Global-Def
  G-Layout-Def : Layout → Global-Def
  G-Adt-Def : Adt → Global-Def

G-Env : Set
G-Env = List (Name × Global-Def)

-- Adt-Constr-Fields : Name → G-Env → List Name

data Base-Type : Type → Set where
  Base-Type-Int : Base-Type Int-Type
  Base-Type-Bool : Base-Type Bool-Type

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

data Name-Subst : Name → Name → Name → Name → Set where
  Name-Subst-≢ : (old new curr : Name) →
    old ≢ curr →
    Name-Subst old new curr curr

  Name-Subst-≡ : (old new : Name) →
    Name-Subst old new old new

data Addr-Name-Subst : Name → Name → Addr → Addr → Set where
  AN-Subst : (old-name new-name : Name) (old-x new-x : Name) (i : ℕ) →
    Name-Subst old-name new-name old-x new-x →
    Addr-Name-Subst old-name new-name (old-x :+ i) (new-x :+ i)

data Heaplet-Name-Subst : Name → Name → Heaplet → Heaplet → Set where
  HN-Subst-:-> : (old-name new-name : Name) (old-x new-x : Addr) (old-y new-y : Name) →
    Addr-Name-Subst old-name new-name old-x new-x →
    Name-Subst old-name new-name old-y new-y →
    Heaplet-Name-Subst old-name new-name (old-x :-> old-y) (new-x :-> new-y)

  HN-Subst-H· : (old-name new-name : Name) (f : Name) (old-args new-args : Name) →
    -- All (λ (old , new) → Name-Subst old-name new-name old new) (Data.List.zip old-args new-args) →
    Name-Subst old-name new-name old-args new-args →
    Heaplet-Name-Subst old-name new-name (f H· old-args) (f H· new-args)

data _,,_▷_⇓[_,_]_ : Fresh-Supply → G-Env → Expr → Addr → Name → SuSLik-Asn → Set

data _▷_,,_⟶constr_ : G-Env → List Layout-Branch → Expr → List SuSLik-Heaplet → Set where
  -- TODO: This needs substitution
  constr-reduce : ∀ {Δ A C args hs suslik-hs} →
    (Mk-Layout-Branch C hs) ∈ A →
    All (λ (h , suslik-h) → →SuSLik-Heaplet h suslik-h) (Data.List.zip hs suslik-hs) →
    Δ ▷ A ,, (C C· args) ⟶constr suslik-hs

data _,,_▷_⇓[_,_]_ where
  ⇓-Var : ∀ {Σ x r v} →
    FS-Empty ,, Σ ▷ Var x ⇓[ r , v ] ((Var v == Var x) ,, [ r :-> Var v ])

  ⇓-Int : ∀ {Σ i r v} →
    FS-Empty ,, Σ ▷ Int-Lit i ⇓[ r , v ] ((Var v == Int-Lit i) ,, [ r :-> Var v ])

  ⇓-Bool : ∀ {Σ b r v} →
    FS-Empty ,, Σ ▷ Bool-Lit b ⇓[ r , v ] ((Var v == Bool-Lit b) ,, [ r :-> Var v ])

  ⇓-Add : ∀ {fr₁ fr₂ Σ e₁ e₂ r v v₁ v₂ s₁ s₂ s₃ s} →
    v₁ ≢ v →
    v₂ ≢ v →
    v₂ ≢ v₁ →
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
    FS-Branch (x ∷ v₁ ∷ []) fr FS-Empty ,, Σ ▷ e ⇓[ x :+ 0 , v₁ ] s₁ →
    FS-Branch (x ∷ v₁ ∷ []) fr FS-Empty ,, Σ ▷ (Instantiate A B f e) ⇓[ r , v ] s

  -- ⇓-Lower-Lower : ∀ {fr Σ A e r v s} →
  --   fr ,, Σ ▷ (Lower A e) ⇓[ r , v ] s →
  --   fr ,, Σ ▷ (Lower A (Lower A e)) ⇓[ r , v ] s

  ⇓-Lower-Var : ∀ {Σ A n r v} →
    FS-Empty ,, Σ ▷ Lower A (Var n) ⇓[ r , v ] ((Addr-Var r == Var n) ,, [])

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

Append-fn : ∀ {A : Set} {xs ys zs : List A} →
  Append xs ys zs →
  zs ≡ xs ++ ys
Append-fn Append-Nil = refl
Append-fn (Append-Cons prf) rewrite Append-fn prf = refl

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

-- ⇓-Deterministic (⇓-Lower-Lower p) (⇓-Lower-Lower q) rewrite ⇓-Deterministic p q = refl
⇓-Deterministic (⇓-Instantiate-Comp x comb1 comb2 p p₁) (⇓-Instantiate-Comp x₃ comb3 comb4 q q₁)
  with Combine-Asns-<> comb1 | Combine-Asns-<> comb2 | Combine-Asns-<> comb3 | Combine-Asns-<> comb4
... | refl | refl | refl | refl rewrite ⇓-Deterministic p q | ⇓-Deterministic p₁ q₁ = refl
⇓-Deterministic ⇓-Lift ⇓-Lift = refl
⇓-Deterministic ⇓-Lower-Var ⇓-Lower-Var = refl

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

fresh-first : ∀ {x xs} →
  proj₁ (fresh (x ∷ xs)) ≢ x
fresh-first {x} {xs} with proj₂ (fresh (x ∷ xs))
... | px ∷ z = λ eq → px (sym eq)

fresh-second : ∀ {x y rest} →
  proj₁ (fresh (x ∷ y ∷ rest)) ≢ y
fresh-second {x} {y} {rest} with proj₂ (fresh (x ∷ y ∷ rest))
... | _ ∷ py ∷ z = λ eq → py (sym eq)

data _,,_▷_∶_ : G-Env → Ty-Env → Expr → Type → Set where
  Type-of-Var : ∀ {Δ Γ n τ} →
    (n , τ) ∈ Γ →
    ---------
    Δ ,, Γ ▷ Var n ∶ τ

  -- Type-of-C·-nil : ∀ {Δ Γ Adt-Name branches C} →
  --   (Adt-Name , G-Adt-Def (Mk-Adt branches)) ∈ Δ →
  --   Mk-Adt-Branch C [] ∈ branches →
  --   Δ ,, Γ ▷ (C C· []) ∶ Adt-Type Adt-Name

  Type-of-C· : ∀ {Δ Γ Adt-Name branches C args τs} →
    (Adt-Name , G-Adt-Def (Mk-Adt branches)) ∈ Δ →
    Mk-Adt-Branch C τs ∈ branches →
    All (λ (arg , τ) → Δ ,, Γ ▷ arg ∶ τ) (Data.List.zip args τs) →
    ---------
    Δ ,, Γ ▷ (C C· args) ∶ Adt-Type Adt-Name

  Type-of-· : ∀ {Δ Γ f-name branches arg τ₁ τ₂} →
    (f-name , G-Fn-Def (Mk-Fn-Def τ₁ τ₂ branches)) ∈ Δ →
    Δ ,, Γ ▷ arg ∶ τ₁ →
    ---------
    Δ ,, Γ ▷ (f-name · arg) ∶ τ₂

  Type-of-Int-Lit : ∀ {Δ Γ i} →
    ---------
    Δ ,, Γ ▷ Int-Lit i ∶ Int-Type

  Type-of-Bool-Lit : ∀ {Δ Γ b} →
    ---------
    Δ ,, Γ ▷ Bool-Lit b ∶ Bool-Type

  Type-of-==-Int : ∀ {Δ Γ e₁ e₂} →
    Δ ,, Γ ▷ e₁ ∶ Int-Type →
    Δ ,, Γ ▷ e₂ ∶ Int-Type →
    ---------
    Δ ,, Γ ▷ (e₁ == e₂) ∶ Int-Type

  Type-of-Add : ∀ {Δ Γ e₁ e₂} →
    Δ ,, Γ ▷ e₁ ∶ Int-Type →
    Δ ,, Γ ▷ e₂ ∶ Int-Type →
    ---------
    Δ ,, Γ ▷ Add e₁ e₂ ∶ Int-Type

  Type-of-Lower : ∀ {Δ Γ A Adt-Name adt-def SuSLik-params branches e} →
    (A , G-Layout-Def (Mk-Layout A (Adt-Name , SuSLik-params) branches)) ∈ Δ →
    (Adt-Name , G-Adt-Def adt-def) ∈ Δ →
    Δ ,, Γ ▷ e ∶ Adt-Type Adt-Name →
    ---------
    Δ ,, Γ ▷ Lower A e ∶ Layout-Type A

  Type-of-Instantiate : ∀ {Δ Γ A B Adt-Name-A Adt-Name-B adt-def-A adt-def-B SuSLik-params-A SuSLik-params-B branches-A branches-B f-branches f-name e} →
    (A , G-Layout-Def (Mk-Layout A (Adt-Name-A , SuSLik-params-A) branches-A)) ∈ Δ →
    (Adt-Name-A , G-Adt-Def adt-def-A) ∈ Δ →

    (B , G-Layout-Def (Mk-Layout B (Adt-Name-B , SuSLik-params-B) branches-B)) ∈ Δ →
    (Adt-Name-B , G-Adt-Def adt-def-B) ∈ Δ →

    (f-name , G-Fn-Def (Mk-Fn-Def (Adt-Type Adt-Name-A) (Adt-Type Adt-Name-B) f-branches)) ∈ Δ →

    Δ ,, Γ ▷ e ∶ (Layout-Type A) →
    ---------
    Δ ,, Γ ▷ (Instantiate A B f-name e) ∶ (Layout-Type B)

_▷_∶_ : G-Env → Expr → Type → Set
Δ ▷ e ∶ τ = Δ ,, [] ▷ e ∶ τ

data _,,_▷_⇒_ : G-Env → Ty-Env → Expr → Type → Set where
  Conc-Type-of-Lower-C· : ∀ {Δ Γ A C args adt-name adt branches τs} →
    (adt-name , G-Adt-Def adt) ∈ Δ →
    Mk-Adt-Branch C τs ∈ branches →
    All (λ (arg , τ) → Δ ,, Γ ▷ arg ⇒ τ) (Data.List.zip args τs) →
    Δ ,, Γ ▷ Lower A (C C· args) ⇒ Layout-Type A

  Conc-Type-of-Instantiate : ∀ {Δ Γ A B Adt-Name-A Adt-Name-B adt-def-A adt-def-B SuSLik-params-A SuSLik-params-B branches-A branches-B f-branches f-name e} →
    (A , G-Layout-Def (Mk-Layout A (Adt-Name-A , SuSLik-params-A) branches-A)) ∈ Δ →
    (Adt-Name-A , G-Adt-Def adt-def-A) ∈ Δ →

    (B , G-Layout-Def (Mk-Layout B (Adt-Name-B , SuSLik-params-B) branches-B)) ∈ Δ →
    (Adt-Name-B , G-Adt-Def adt-def-B) ∈ Δ →

    (f-name , G-Fn-Def (Mk-Fn-Def (Adt-Type Adt-Name-A) (Adt-Type Adt-Name-B) f-branches)) ∈ Δ →

    Δ ,, Γ ▷ e ⇒ (Layout-Type A) →
    ---------
    Δ ,, Γ ▷ (Instantiate A B f-name e) ⇒ (Layout-Type B)


  -- Type-of-· : ∀ {Δ Γ f-name branches arg τ₁ τ₂} →
  --   (f-name , G-Fn-Def (Mk-Fn-Def τ₁ τ₂ branches)) ∈ Δ →
  --   Δ ,, Γ ▷ arg ⇒ τ₁ →
  --   ---------
  --   Δ ,, Γ ▷ (f-name · arg) ⇒ τ₂

  Type-of-Int-Lit : ∀ {Δ Γ i} →
    ---------
    Δ ,, Γ ▷ Int-Lit i ⇒ Int-Type

  Type-of-Bool-Lit : ∀ {Δ Γ b} →
    ---------
    Δ ,, Γ ▷ Bool-Lit b ⇒ Bool-Type

  Type-of-==-Int : ∀ {Δ Γ e₁ e₂} →
    Δ ,, Γ ▷ e₁ ⇒ Int-Type →
    Δ ,, Γ ▷ e₂ ⇒ Int-Type →
    ---------
    Δ ,, Γ ▷ (e₁ == e₂) ⇒ Int-Type

  Type-of-Add : ∀ {Δ Γ e₁ e₂} →
    Δ ,, Γ ▷ e₁ ⇒ Int-Type →
    Δ ,, Γ ▷ e₂ ⇒ Int-Type →
    ---------
    Δ ,, Γ ▷ Add e₁ e₂ ⇒ Int-Type

  -- Conc-Type-base : ∀ {Δ Γ e} →
  --   Type-of

_▷_⇒_ : G-Env → Expr → Type → Set
Δ ▷ e ⇒ τ = Δ ,, [] ▷ e ⇒ τ

data Concrete-Type : Type → Set where
  Layout-Concrete : ∀ {n} → Concrete-Type (Layout-Type n)
  Bool-Concrete : Concrete-Type Bool-Type
  Int-Concrete : Concrete-Type Int-Type


is-Concrete-Type : ∀ {Δ Γ e τ} →
  Δ ,, Γ ▷ e ⇒ τ →
  Concrete-Type τ
is-Concrete-Type {_} {_} {e} {Int-Type} prf = Int-Concrete
is-Concrete-Type {_} {_} {e} {Bool-Type} prf = Bool-Concrete
is-Concrete-Type {_} {_} {e} {τ ⟶ τ₁} ()
is-Concrete-Type {_} {_} {e} {Adt-Type x} ()
is-Concrete-Type {_} {_} {e} {Layout-Type x} prf = Layout-Concrete

⇓-Total : ∀ {env e r v τ} →
  env ▷ e ⇒ τ →
  Σ Fresh-Supply λ fr →
  Σ SuSLik-Asn λ s →
    fr ,, env ▷ e ⇓[ r , v ] s
⇓-Total {env} {Bool-Lit x} {r} {v} {τ} prf = FS-Empty , ((Var v == Bool-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Bool
⇓-Total {env} {Int-Lit x} {r} {v} {τ} prf = FS-Empty , ((Var v == Int-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Int
⇓-Total {env} {e == e₁} {r} {v} {.Int-Type} (Type-of-==-Int prf prf₁) =
  let v₁ , v₁-prf = fresh [ v ]
      v₂ , v₂-prf = fresh (v ∷ v₁ ∷ [])

      left = ⇓-Total {env} {e} {Unused-Addr} {v₁} prf
      right = ⇓-Total {env} {e₁} {Unused-Addr} {v₂} prf₁

      s₁ = proj₁ (proj₂ left)
      s₂ = proj₁ (proj₂ right)

      asn = ((Var v == ((Var v₁) == (Var v₂))) ,, []) <> s₁ <> s₂
  in
  FS-Branch (v₁ ∷ v₂ ∷ []) (proj₁ left) (proj₁ right) , asn , ⇓-== fresh-first fresh-first fresh-second Combine-Asns-exists Combine-Asns-exists (proj₂ (proj₂ left)) (proj₂ (proj₂ right))
⇓-Total {env} {Add e e₁} {r} {v} {.Int-Type} (Type-of-Add prf prf₁) =
  let v₁ , v₁-prf = fresh [ v ]
      v₂ , v₂-prf = fresh (v ∷ v₁ ∷ [])

      left = ⇓-Total {env} {e} {Unused-Addr} {v₁} prf
      right = ⇓-Total {env} {e₁} {Unused-Addr} {v₂} prf₁

      s₁ = proj₁ (proj₂ left)
      s₂ = proj₁ (proj₂ right)

      asn = ((Var v == (Add (Var v₁) (Var v₂))) ,, []) <> s₁ <> s₂
  in
  FS-Branch (v₁ ∷ v₂ ∷ []) (proj₁ left) (proj₁ right) , asn , ⇓-Add fresh-first fresh-first fresh-second Combine-Asns-exists Combine-Asns-exists (proj₂ (proj₂ left)) (proj₂ (proj₂ right))
⇓-Total {env} {Lower x (x₁ C· x₂)} {r} {v} {τ} prf = {!!} , ({!!} , {!!})
⇓-Total {env} {Instantiate x x₁ x₂ e} {r} {v} {τ} prf = {!!}
-- ⇓-Total {env} {Var x} {r} {v} prf = FS-Empty , ((Var v == Var x) ,, ((r :-> Var v) ∷ [])) , ⇓-Var
-- ⇓-Total {env} {x C· x₁} {r} {v} (Type-of-C· x₂ x₃ x₄) = {!!}
-- ⇓-Total {env} {x · e} {r} {v} prf = {!!}
-- ⇓-Total {env} {Bool-Lit x} {r} {v} prf = FS-Empty , ((Var v == Bool-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Bool
-- ⇓-Total {env} {Int-Lit x} {r} {v} prf = FS-Empty , ((Var v == Int-Lit x) ,, ((r :-> Var v) ∷ [])) , ⇓-Int

-- ⇓-Total {env} {e == e₁} {r} {v} (Type-of-==-Int prf prf₁) =
--   let v₁ , v₁-prf = fresh [ v ]
--       v₂ , v₂-prf = fresh (v ∷ v₁ ∷ [])

--       left = ⇓-Total {env} {e} {Unused-Addr} {v₁} prf
--       right = ⇓-Total {env} {e₁} {Unused-Addr} {v₂} prf₁

--       s₁ = proj₁ (proj₂ left)
--       s₂ = proj₁ (proj₂ right)

--       asn = ((Var v == ((Var v₁) == (Var v₂))) ,, []) <> s₁ <> s₂
--   in
--   FS-Branch (v₁ ∷ v₂ ∷ []) (proj₁ left) (proj₁ right) , asn , ⇓-== fresh-first fresh-first fresh-second Combine-Asns-exists Combine-Asns-exists (proj₂ (proj₂ left)) (proj₂ (proj₂ right))
-- ⇓-Total {env} {Add e e₁} {r} {v} prf = {!!}
-- ⇓-Total {env} {Lower x e} {r} {v} prf = {!!}
-- ⇓-Total {env} {Instantiate x x₁ x₂ e} {r} {v} prf = {!!}
-- ⇓-Total {env} {Lift x} {r} {v} prf = FS-Empty ,
--                                    (((Var v == Addr-Var r) && (Addr-Var r == Addr-Var x)) ,, []) ,
--                                    ⇓-Lift

-- Exprs-FVs : Name → List Expr → List Name

-- Expr-FVs : Name → Expr → List Name
-- Expr-FVs param (Var x) with Name-eq-dec {param} {x}
-- ... | inj₁ refl = []
-- ... | inj₂ y = [ x ]
-- Expr-FVs param (x C· x₁) = Exprs-FVs param x₁
-- Expr-FVs param (x · e) = Expr-FVs param e
-- Expr-FVs param (Bool-Lit x) = []
-- Expr-FVs param (Int-Lit x) = []
-- Expr-FVs param (e == e₁) = Expr-FVs param e ++ Expr-FVs param e₁
-- Expr-FVs param (Add e e₁) = Expr-FVs param e ++ Expr-FVs param e₁
-- Expr-FVs param (Lower x e) = Expr-FVs param e
-- Expr-FVs param (Instantiate x x₁ x₂ e) = Expr-FVs param e
-- Expr-FVs param (Lift x) = []

-- Exprs-FVs param [] = []
-- Exprs-FVs param (x ∷ exprs) = Expr-FVs param x ++ Exprs-FVs param exprs

-- Name-without : Name → Name → List Name
-- Name-without param x with Name-eq-dec {param} {x}
-- ... | inj₁ refl = []
-- ... | inj₂ y = [ x ]


-- Heaplet-FVs : Name → Heaplet → List Name
-- Heaplet-FVs param ((x :+ x₂) :-> x₁) = Name-without param x ++ Name-without param x₁
-- Heaplet-FVs param (Unused-Addr :-> x₁) = Name-without param x₁
-- Heaplet-FVs param (x H· x₁) = Name-without param x₁


-- Layout-Branch-FVs : Name → Layout-Branch → List Name
-- Layout-Branch-FVs param (Mk-Layout-Branch x x₁) = concatMap (Heaplet-FVs param) x₁

-- Layout-FVs : Layout → List Name
-- Layout-FVs (Mk-Layout x (fst , param) branches) = concatMap (Layout-Branch-FVs param) branches

-- Name-subst : Name → Name → Name → Name
-- Name-subst old new x with Name-eq-dec {old} {x}
-- ... | inj₁ refl = new
-- ... | inj₂ p = x

-- Name-subst-Heaplet : Name → Name → Heaplet → Heaplet
-- Name-subst-Heaplet old new ((x :+ x₂) :-> x₁) = (Name-subst old new x :+ x₂) :-> (Name-subst old new x₁)
-- Name-subst-Heaplet old new (Unused-Addr :-> x₁) = Unused-Addr :-> Name-subst old new x₁
-- Name-subst-Heaplet old new (x H· x₁) = x H· Name-subst old new x₁

-- Layout-Branch-Heaplets : Layout-Branch → List Heaplet
-- Layout-Branch-Heaplets (Mk-Layout-Branch x x₁) = x₁

-- S[_,_]⟦_⟧_ : Name  → Name → Expr → G-Env → SuSLik-Asn
-- S[ r-name , v ]⟦ e ⟧ env with ⇓-Total {env} {e} {r-name :+ 0} {v} {!!}
-- ... | fst , fst₁ , snd = fst₁

-- T[_]⟦_⟧_ : (arg : Name) → (layout : Layout) → ¬ (arg ∈ Layout-FVs layout) → List (List SuSLik-Heaplet)
-- T[ r-name ]⟦ Mk-Layout x (x₁ , param) x₂ ⟧ prf = (Data.List.map (λ x₃ → (Data.List.map →SuSLik-Heaplet (Data.List.map (Name-subst-Heaplet param r-name) (Layout-Branch-Heaplets x₃)))) x₂)

-- -- TODO: Is this how we should deal with the guards?
-- -- Also, is it okay to do naive substitution here? It seems like Fn-Defs shouldn't have any free variables that could be captured
-- Fn-Def-Apply : (fn-def : Fn-Def) → Name → List Expr → List Guard-Branch
-- Fn-Def-Apply fn-def C C-args = {!!}

-- -- TODO: Add a thing to check that a global environment is valid and well-typed

-- -- data G-Env-Valid : G-Env → G-Env → Set where

-- -- A simplified version
-- data _-*_ : List SuSLik-Heaplet → List SuSLik-Heaplet → Set where
--   wand-emp : ∀ {hs} → [] -* hs
--   wand-cons : ∀ {h hs hs₂} →
--     h ∈ hs₂ →
--     hs -* hs₂ →
--     (h ∷ hs) -* hs₂

-- data _▷_÷_ : G-Env → SuSLik-Asn → List (List SuSLik-Heaplet) → Set where
--   LL-Type-of-exists : ∀ {Δ pure-part spatial-part hs hss} →
--     hs ∈ hss →
--     hs -* spatial-part →
--     Δ ▷ (pure-part ,, spatial-part) ÷ hss

-- high→low-level : ∀ {Δ e r v layout-name layout} →
--   (layout-name , G-Layout-Def layout) ∈ Δ →
--   (prf : ¬ (r ∈ Layout-FVs layout)) →

--   Δ ▷ e ∶ Layout-Type layout-name →
--   Δ ▷ (S[ r , v ]⟦ e ⟧ Δ) ÷ (T[ r ]⟦ layout ⟧ prf)
-- -- high→low-level {Δ} {_} {r} {v} prf1 prf2 (Type-of-· {_} {_} {f-name} {_} {arg} x prf3) with S[ r , v ]⟦ f-name · arg ⟧ Δ
-- -- ... | x₁ ,, x₂ = {!!} --LL-Type-of-exists {!!} {!!}
-- high→low-level {Δ} {e} {r} {v} prf1 prf2 (Type-of-· {_} {_} {f-name} {_} {arg} x prf3) with ⇓-Total {Δ} {e} {r :+ 0} {v} {!!}
-- ... | ()
-- high→low-level {((layout-name , G-Layout-Def layout) ∷ xs)} {Lower layout-name e} {r} {v} {layout-name} (here refl) prf2 (Type-of-Lower x y prf3)
--   with ⇓-Total {(layout-name , G-Layout-Def layout) ∷ xs} {e} {r :+ 0} {v} {!!}
-- ... | fst , fst₁ , snd = LL-Type-of-exists {!!} {!!}
-- high→low-level {.(_ ∷ _)} {Lower layout-name e} {r} {v} {layout-name} (there prf1) prf2 (Type-of-Lower x y prf3) = {!!}
-- -- ... | .FS-Empty , .((Var v == Var _) ,, [ (r :+ 0) :-> Var v ]) , ⇓-Var = LL-Type-of-exists {!!} {!!}
-- -- ... | x₁ ,, x₂ = {!!} -- LL-Type-of-exists {!!} {!!}
-- high→low-level prf1 prf2 (Type-of-Instantiate x x₁ x₂ x₃ x₄ prf3) = {!!}

-- data _,,_▷_⟼_ : G-Env → Ty-Env → Expr → Expr → Set where
--   Small-step-· : ∀ {Δ Γ f fn-def C es} →
--     (f , G-Fn-Def fn-def) ∈ Δ →
--     Δ ,, Γ ▷ (f · (C C· es)) ⟼ {!!}

--   Small-step-Add : ∀ {Δ Γ i j} →
--     Δ ,, Γ ▷ Add (Int-Lit i) (Int-Lit j) ⟼ Int-Lit (i Data.Integer.+ j)

--   Small-step-== : ∀ {Δ Γ i j} →
--     Δ ,, Γ ▷ (Int-Lit i == Int-Lit j) ⟼ Bool-Lit (isYes (i Data.Integer.≟ j))

--   Small-step-Instantiate : ∀ {Δ Γ f A B e} →
--     Δ ,, Γ ▷ (Instantiate A B f e) ⟼ (f · e)

--   Small-step-Lower : ∀ {Δ Γ A e} →
--     Δ ,, Γ ▷ (Lower A e) ⟼ e

-- data _,,_▷_⟼*_ : G-Env → Ty-Env → Expr → Expr → Set where
--   Small-steps-refl : ∀ {Δ Γ e} →
--     Δ ,, Γ ▷ e ⟼* e

--   Small-steps-trans : ∀ {Δ Γ e e′ e′′} →
--     Δ ,, Γ ▷ e ⟼ e′ →
--     Δ ,, Γ ▷ e′ ⟼* e′′ →
--     Δ ,, Γ ▷ e ⟼* e′′

