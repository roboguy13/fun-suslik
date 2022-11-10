module Syntax.Simple.IsNullTranslation
  (translateIsNull)
  where

import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik
import           Syntax.Simple.ToSuSLik
import           Syntax.Name
import           Syntax.FreshGen

import           Control.Arrow (first)
import           Control.Monad
import           Control.Applicative

import           Data.Foldable
import           Data.Maybe

translateIsNull :: [Layout] -> DefWithAsn -> DefWithAsn
translateIsNull layouts def =
  def
  { defBranches = map branchTranslate (defBranches def)
  }
  where
    branchTranslate :: DefBranchWithAsn -> DefBranchWithAsn
    branchTranslate branch =
      branch
      { defBranchGuardeds = map (guardedTranslate (defBranchPatterns branch)) (defBranchGuardeds branch)
      }

    guardedTranslate :: [Pattern' ParamTypeP] -> GuardedExprWithAsn -> GuardedExprWithAsn
    guardedTranslate pats (MkGuardedExpr cond body) =
      MkGuardedExpr
        cond
        (goAsn body)

    goAsn :: ExprWithAsn FsName -> ExprWithAsn FsName
    goAsn (MkExprWithAsn asn e) =
      MkExprWithAsn (fromMaybe asn (go e)) e

    go :: ElaboratedExpr FsName -> Maybe (Assertion FsName)
    go e0@(Var ty v) = Nothing
    go e0@(IntLit i) = Nothing
    go e0@(BoolLit b) = Nothing

    go (And x y) = go x <|> go y
    go (Or x y) = go x <|> go y
    go (Not x) = go x

    go (Add x y) = go x <|> go y
    go (Sub x y) = go x <|> go y
    go (Mul x y) = go x <|> go y

    go (Equal x y) = go x <|> go y
    go (Le x y) = go x <|> go y
    go (Lt x y) = go x <|> go y

    go (Apply fName outLayout inLayouts args) =
      foldr (<|>) Nothing (map go args)

    go (ConstrApply ty@(LayoutParam lName) cName args) =
      case lookupLayoutBranch (lookupLayout layouts (baseLayoutName (getParamedName lName))) cName of
        (_, Emp) ->
          let [v] = loweredParams ty
          in
          Just $ IsNull v
        _ -> Nothing
        -- _ -> ConstrApply ty cName (map go args)

