--
-- Stage 5 here https://github.com/roboguy13/fun-suslik/blob/d5ccdc275ff13473f8e11af34deb8ce3523f6a9f/README.md
--

{-# LANGUAGE LiberalTypeSynonyms #-}

module Syntax.Simple.UnfoldConstructors
  (unfoldConstructors)
  where

import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik
import           Syntax.Name

import           Control.Arrow (first)

type SuSLikExpr' = SuSLikExpr SuSLikName

unfoldConstructors :: DefWithAsn -> AsnDef
unfoldConstructors def =
  def
  { defBranches = map branchTranslate (defBranches def)
  }
  where
    branchTranslate :: DefBranchWithAsn -> AsnDefBranch
    branchTranslate branch =
      branch
      { defBranchGuardeds = map guardedTranslate (defBranchGuardeds branch)
      }

    guardedTranslate :: GuardedExprWithAsn -> AsnGuarded
    guardedTranslate (MkGuardedExpr cond (MkExprWithAsn asn bodyExpr)) =
      let (_, bodyAsn) = exprTranslate bodyExpr
      in
      MkGuardedExpr cond (asn <> bodyAsn)

    exprTranslate :: ElaboratedExpr FsName -> ([SuSLikExpr SuSLikName], Assertion SuSLikName)
    exprTranslate (Var ty v) = (map VarS (loweredParams ty), Emp)
    exprTranslate (IntLit i) = ([IntS i], Emp)
    exprTranslate (BoolLit b) = ([BoolS b], Emp)

    exprTranslate (And x y) = combineBin' AndS x y
    exprTranslate (Or x y) = combineBin' OrS x y
    exprTranslate (Not x) = first (map NotS) $ exprTranslate x

    exprTranslate (Add x y) = combineBin' AddS x y
    exprTranslate (Sub x y) = combineBin' SubS x y
    exprTranslate (Mul x y) = combineBin' MulS x y

    exprTranslate (Equal x y) = combineBin' EqualS x y
    exprTranslate (Le x y) = combineBin' LeS x y
    exprTranslate (Lt x y) = combineBin' LtS x y

    exprTranslate (Apply fName outLayout inLayouts args) =
      let (exprs, asns) = first concat $ unzip $ map exprTranslate args
          asn = mconcat asns
      in
      (map VarS (loweredParams outLayout)
      ,HeapletApply (MkLayoutName Nothing fName) (exprs ++ map VarS (loweredParams outLayout)) [] asn
      )

    exprTranslate (ConstrApply layout cName args) =
      let (exprs, asns) = first concat $ unzip $ map exprTranslate args
          asn = mconcat asns
      in
      (map VarS (loweredParams layout)
      ,asn
      )

    combineBin' op x y = combineBin op (exprTranslate x) (exprTranslate y)

combineBin :: (SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr') ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName)
combineBin op (es1, asns1) (es2, asns2) =
  (zipWith op es1 es2, asns1 <> asns2)

