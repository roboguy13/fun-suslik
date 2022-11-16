{-# OPTIONS_GHC -Wall #-}

module Syntax.Simple.TranslateLets
  (translateLets)
  where

import           Syntax.Simple.Heaplet
import           Syntax.Name

import           Control.Monad.Writer
import           Control.Applicative

import           Data.Void

import Debug.Trace

translateLets :: DefWithAsn -> DefWithAsn
translateLets def =
  def
  { defBranches = map branchTranslate (defBranches def)
  }
  where
    branchTranslate :: DefBranchWithAsn -> DefBranchWithAsn
    branchTranslate branch =
      branch
      { defBranchGuardeds = map guardedTranslate (defBranchGuardeds branch)
      }

    guardedTranslate :: GuardedExprWithAsn -> GuardedExprWithAsn
    guardedTranslate (MkGuardedExpr cond (MkExprWithAsn asn body)) =
      let (body', newAsn) = runWriter $ go body
      in
      MkGuardedExpr
        cond
        (MkExprWithAsn
          (asn <> newAsn)
          body')

    go :: ElaboratedExpr FsName -> Writer (Assertion FsName) (ElaboratedExpr FsName)
    go e@(Var {}) = pure e
    go e@(IntLit {}) = pure e
    go e@(BoolLit {}) = pure e
    go (And x y) = liftA2 And (go x) (go y)
    go (Or x y) = liftA2 Or (go x) (go y)
    go (Not x) = Not <$> go x
    go (Add x y) = liftA2 Add (go x) (go y)
    go (Sub x y) = liftA2 Sub (go x) (go y)
    go (Mul x y) = liftA2 Mul (go x) (go y)
    go (Equal x y) = liftA2 Equal (go x) (go y)
    go (Le x y) = liftA2 Le (go x) (go y)
    go (Lt x y) = liftA2 Lt (go x) (go y)
    go (Apply f a b args) =
      Apply f a b <$> mapM go args
    go (ConstrApply ty cName args) =
      ConstrApply ty cName <$> mapM go args
    go (Lower x _) = absurd x
    go (Instantiate _ x _ _) = absurd x
    go (Deref ty x) = Deref ty <$> go x
    go (Addr ty x) = Addr ty <$> go x
    go (LetIn ty v rhs body) = do
      tell $ AssertEqual v (toSuSLikExpr "" rhs) Emp

      pure body -- NOTE: We eliminate the LetIn here

      -- LetIn ty v <$> go rhs <*> go body

