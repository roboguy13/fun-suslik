--
-- Stage 5 here https://github.com/roboguy13/fun-suslik/blob/d5ccdc275ff13473f8e11af34deb8ce3523f6a9f/README.md
--

{-# LANGUAGE LiberalTypeSynonyms #-}

module Syntax.Simple.UnfoldConstructors
  (unfoldConstructors)
  where

import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik
import           Syntax.Simple.ToSuSLik
import           Syntax.Name
import           Syntax.FreshGen

import           Control.Arrow (first)
import           Control.Monad

import           Data.Foldable

import Debug.Trace

type SuSLikExpr' = SuSLikExpr SuSLikName

unfoldConstructors :: [Layout] -> DefWithAsn -> AsnDef
unfoldConstructors layouts def =
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
      let (_, bodyAsn) = snd . runFreshGen $ exprTranslate Nothing bodyExpr
      in
      MkGuardedExpr cond (asn <> bodyAsn)

    -- -- | Keep unfolding any HeapletApply to a known constructor application
    -- unfoldAssertion :: Assertion FsName -> Assertion FsName
    -- unfoldAssertion Emp = Emp
    -- unfoldAssertion (PointsTo mode x y rest) =
    --   PointsTo mode x y (unfoldAssertion rest)
    -- unfoldAssertion

    -- -- | Remove any HeapletApply that has an empty SuSLik arg list
    -- removeEmptyApplies :: Assertion FsName -> Assertion FsName
    -- removeEmptyApplies 

    exprTranslate :: Maybe [SuSLikName] -> ElaboratedExpr FsName -> FreshGen ([SuSLikExpr SuSLikName], Assertion SuSLikName)
    exprTranslate _ (Var ty v) = pure (map VarS (loweredParams ty), Emp)
    exprTranslate _ (IntLit i) = pure ([IntS i], Emp)
    exprTranslate _ (BoolLit b) = pure ([BoolS b], Emp)

    exprTranslate out (And x y) = combineBin' out AndS x y
    exprTranslate out (Or x y) = combineBin' out OrS x y
    exprTranslate out (Not x) = first (map NotS) <$> exprTranslate out x

    exprTranslate out (Add x y) = combineBin' out AddS x y
    exprTranslate out (Sub x y) = combineBin' out SubS x y
    exprTranslate out (Mul x y) = combineBin' out MulS x y

    exprTranslate out (Equal x y) = combineBin' out EqualS x y
    exprTranslate out (Le x y) = combineBin' out LeS x y
    exprTranslate out (Lt x y) = combineBin' out LtS x y

    exprTranslate out (Apply fName outLayout inLayouts args) = do
      (exprs, asns) <- first concat . unzip <$> mapM (exprTranslate (Just $ loweredParams outLayout)) args
      let asn = mconcat asns
      pure (map VarS (loweredParams outLayout),
       HeapletApply (MkLayoutName Nothing fName) (exprs ++ map VarS (loweredParams outLayout)) [] asn)

    exprTranslate out e@(ConstrApply ty@(LayoutParam layoutName) cName args) = do
      (_, asns) <- first concat . unzip <$> mapM (exprTranslate (Just $ getParamedNameParams layoutName)) args
      let asn = mconcat asns
          layout = lookupLayout layouts (baseLayoutName (getParamedName layoutName))
          -- suslikParams = concatMap getOutParams args

          exprs = foldMap toList $ concatMap getOutParams args -- TODO: Generalize this to work with more kinds of expressions

      suslikParams <-
        case out of
          -- Nothing -> genLayoutParams layout
          Nothing -> pure $ getParamedNameParams layoutName
          Just outVars -> pure outVars

      let matched = removeHeapletApplies $ applyLayout layout suslikParams cName exprs

      pure (map VarS suslikParams
            ,asn <> setAssertionMode Output matched
            )

    combineBin' out op x y = combineBin op <$> (exprTranslate out x) <*> (exprTranslate out y)

combineBin :: (SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr') ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName)
combineBin op (es1, asns1) (es2, asns2) =
  (zipWith op es1 es2, asns1 <> asns2)

getOutParams :: ElaboratedExpr FsName -> [SuSLikExpr SuSLikName]
getOutParams (Var (LayoutParam paramedName) v) =
  map VarS $ getParamedNameParams paramedName
getOutParams (Var _ v) = [VarS v]
getOutParams (IntLit i) = [IntS i]
getOutParams (BoolLit b) = [BoolS b]
getOutParams (And x y) = getOutParamsBin AndS x y
getOutParams (Or x y) = getOutParamsBin OrS x y
getOutParams (Not x) =
  let [x'] = getOutParams x
  in
  [NotS x']

getOutParams (Add x y) = getOutParamsBin AddS x y
getOutParams (Sub x y) = getOutParamsBin SubS x y
getOutParams (Mul x y) = getOutParamsBin MulS x y

getOutParams (Equal x y) = getOutParamsBin EqualS x y
getOutParams (Le x y) = getOutParamsBin LeS x y
getOutParams (Lt x y) = getOutParamsBin LtS x y

getOutParams (Apply f outTy inTys args) =
  map VarS (loweredParams outTy)

getOutParams (ConstrApply ty cName args) = 
  map VarS (loweredParams ty)

-- getOutParams (And {}) = genIntermediate

getOutParamsBin ::
  (SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr') ->
  ElaboratedExpr FsName ->
  ElaboratedExpr FsName ->
  [SuSLikExpr']
getOutParamsBin op x y =
  let [x'] = getOutParams x
      [y'] = getOutParams y
  in
  [op x' y']
--
--
-- combineBin :: (SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr') ->
--   ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
--   ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
--   ([SuSLikExpr SuSLikName], Assertion SuSLikName)
-- combineBin op (es1, asns1) (es2, asns2) =
--   (zipWith op es1 es2, asns1 <> asns2)
--
-- getOutParams :: ElaboratedExpr FsName -> ElaboratedExpr FsName
-- -- getOutParams (Var (LayoutConcrete paramedName) v) =
-- --   map (\x -> Var _ _) $ getParamedNameParams paramedName
-- getOutParams e@(Var {}) = e
-- getOutParams e@(IntLit {}) = e
-- getOutParams e@(BoolLit {}) = e
-- getOutParams (And x y) = getOutParamsBin And x y
-- getOutParams (Or x y) = getOutParamsBin Or x y
-- getOutParams (Not x) = Not $ getOutParams x
--
-- getOutParams (Add x y) = getOutParamsBin Add x y
-- getOutParams (Sub x y) = getOutParamsBin Sub x y
-- getOutParams (Mul x y) = getOutParamsBin Mul x y
--
-- getOutParams (Equal x y) = getOutParamsBin Equal x y
-- getOutParams (Le x y) = getOutParamsBin Le x y
-- getOutParams (Lt x y) = getOutParamsBin Lt x y
--
-- getOutParams (Apply f outTy inTys args) =
--   Var outTy "$unused"
--
-- getOutParams (ConstrApply ty cName args) = 
--   Var ty "$unused"
--
-- -- getOutParams (And {}) = genIntermediate
--
-- getOutParamsBin ::
--   (ElaboratedExpr FsName -> ElaboratedExpr FsName -> ElaboratedExpr FsName) ->
--   ElaboratedExpr FsName ->
--   ElaboratedExpr FsName ->
--   ElaboratedExpr FsName
-- getOutParamsBin op x y =
--   op (getOutParams x) (getOutParams y)

genLayoutParams :: Layout -> FreshGen [String]
genLayoutParams layout =
  -- uniq <- getUniq
  -- if uniq == 0
  --   then pure "__
  mapM (getFreshWith . ("__y_" <>)) $ layoutSuSLikParams layout

