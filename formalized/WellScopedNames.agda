-- From https://jesper.sikanda.be/posts/1001-syntax-representations.html

module WellScopedNames where
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.List
  open import Data.String

  Scope = List String

  data Term (s : Scope) : Set where
    var : (x : String) → x ∈ s → Term s
    lam : (x : String) → Term (x ∷ s) → Term s
    app : Term s → Term s → Term s
