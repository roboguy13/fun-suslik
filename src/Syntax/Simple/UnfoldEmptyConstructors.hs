{-# LANGUAGE LiberalTypeSynonyms #-}

module Syntax.Simple.UnfoldEmptyConstructors
  (unfoldEmptyConstructors)
  where

import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik
import           Syntax.Simple.ToSuSLik
import           Syntax.Name
import           Syntax.FreshGen

import           Control.Arrow (first)
import           Control.Monad

import           Data.Foldable

unfoldEmptyConstructors :: [Layout] -> NamedDef -> NamedDef
unfoldEmptyConstructors layouts def =
  def
  { defBranches = map branchTranslate (defBranches def)
  }
  where
    branchTranslate :: NamedDefBranch -> NamedDefBranch
    branchTranslate branch =
      branch
      { defBranchGuardeds = map (guardedTranslate (defBranchPatterns branch)) (defBranchGuardeds branch)
      }

    guardedTranslate :: [Pattern' ParamTypeP] -> Named GuardedExpr -> Named GuardedExpr
    guardedTranslate pats (MkGuardedExpr cond body) =
      MkGuardedExpr
        (go cond)
        (go body)

    go :: Named ExprX FsName -> Named ExprX FsName
    go e0@(Var ty v) = e0
    go e0@(IntLit i) = e0
    go e0@(BoolLit b) = e0

    go (And x y) = And (go x) (go y)
    go (Or x y) = Or (go x) (go y)
    go (Not x) = Not (go x)

    go (Add x y) = Add (go x) (go y)
    go (Sub x y) = Sub (go x) (go y)
    go (Mul x y) = Mul (go x) (go y)

    go (Equal x y) = Equal (go x) (go y)
    go (Le x y) = Le (go x) (go y)
    go (Lt x y) = Lt (go x) (go y)

    go (Apply fName outLayout inLayouts args) =
      Apply fName outLayout inLayouts (map go args)

    go (ConstrApply ty@(LayoutParam lName) cName args) =
      case lookupLayoutBranch (lookupLayout layouts (baseLayoutName (getParamedName lName))) cName of
        (_, Emp) -> IntLit 0
        _ -> ConstrApply ty cName (map go args)

    go (Deref ty x) = Deref ty (go x)
    go (Addr ty x) = Addr ty (go x)
    go (LetIn ty v rhs body) =
      LetIn ty v (go rhs) (go body)
    go (IfThenElse ty c t f) =
      IfThenElse ty (go c) (go t) (go f)

