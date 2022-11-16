--
-- Stage 5 here https://github.com/roboguy13/fun-suslik/blob/d5ccdc275ff13473f8e11af34deb8ce3523f6a9f/README.md
--

{-# LANGUAGE LiberalTypeSynonyms #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Syntax.Simple.UnfoldConstructors
  (unfoldConstructors)
  where

import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik
import           Syntax.Simple.ToSuSLik
import           Syntax.Name
import           Syntax.Ppr
import           Syntax.FreshGen

import           Control.Arrow (first)
import           Control.Monad
import           Control.Applicative

import           Control.Monad.Writer

import           Data.Foldable

import           Data.Void

import Debug.Trace

type SuSLikExpr' = SuSLikExpr SuSLikName

isBaseParam :: ParamType' a -> Bool
isBaseParam PtrParam{} = False -- Is this correct?
isBaseParam IntParam{} = True
isBaseParam BoolParam{} = True
isBaseParam LayoutParam{} = False

isBaseType :: ElaboratedExpr a -> Bool
isBaseType (Var ty _) = isBaseParam ty
isBaseType IntLit{} = True
isBaseType BoolLit{} = True
isBaseType (And {}) = True
isBaseType (Or {}) = True
isBaseType (Not {}) = True
isBaseType (Add {}) = True
isBaseType (Sub {}) = True
isBaseType (Mul {}) = True
isBaseType (Equal {}) = True
isBaseType (Le {}) = True
isBaseType (Lt {}) = True
-- isBaseType (Apply _ ty _ _) = isBaseParam ty
isBaseType (Apply _ ty _ _) = False
isBaseType (ConstrApply {}) = False
isBaseType (Deref {}) = True
isBaseType (Addr {}) = False -- TODO: Is this correct?
isBaseType (Lower ty _) = absurd ty
isBaseType (Instantiate _ x _ _) = absurd x

getApplies :: ElaboratedExpr a -> FreshGenT (Writer (Assertion SuSLikName)) [(String, ParamTypeP, [ParamTypeP], [ElaboratedExpr a])]
getApplies (Var ty _) = pure []
getApplies IntLit{} = pure []
getApplies BoolLit{} = pure []
getApplies (And x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Or x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Not x) = getApplies x
getApplies (Add x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Sub x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Mul x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Equal x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Le x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Lt x y) = liftA2 (++) (getApplies x) (getApplies y)
getApplies (Apply f outTy argTys args)
  | length (loweredParams outTy) /= 1 = error $ "getApplies: Expected one parameter in type " ++ show outTy
  | otherwise = do
    ---- Create intermediate variables
    temp <- getFreshWith "__temp_"
    let [orig] = loweredParams outTy

    lift $ tell $ AssertEqual temp (VarS orig) Emp

    --   -- TODO: Use temp points-to here?
    -- lift $ tell (PointsTo Output (Here temp) (VarS orig) Emp)
    -- lift $ tell (TempLoc temp Emp)

    (((f, overwriteParams [temp] outTy, argTys, args) :) . concat) <$> mapM getApplies args
getApplies (ConstrApply ty cName args) = concat <$> mapM getApplies args
getApplies (Deref _ e) = getApplies e
getApplies (Addr _ e) = getApplies e
getApplies (Lower ty _) = absurd ty
getApplies (Instantiate _ x _ _) = absurd x

setVar :: (SuSLikName, ParamTypeP) -> ElaboratedExpr FsName -> Assertion FsName
setVar (v, pTy) rhs =
  case (pTy, getType rhs) of
    (PtrParam {}, Right (PtrParam {})) -> equal -- TODO: Is this correct? Should this be a copy?
    (PtrParam {}, _) -> PointsTo Output (Here v) suslikRhs Emp
    _ -> equal
  where
    suslikRhs = toSuSLikExpr "" rhs
    equal = AssertEqual v suslikRhs Emp

unfoldConstructors :: [Layout] -> DefWithAsn -> AsnDef
unfoldConstructors layouts def =
  def
  { defBranches = map branchTranslate (defBranches def)
  }
  where
    (_, resultType) = defType def

    branchTranslate :: DefBranchWithAsn -> AsnDefBranch
    branchTranslate branch =
      branch
      { defBranchGuardeds = map guardedTranslate (defBranchGuardeds branch)
      }

    guardedTranslate :: GuardedExprWithAsn -> AsnGuarded
    guardedTranslate (MkGuardedExpr cond (MkExprWithAsn asn bodyExpr))
      | isBaseType bodyExpr =
          let toApply (f, outTy, argTys, args) = Apply f outTy argTys args
              (applies, tempsAsn) = runWriter (fmap snd (runFreshGenT (getApplies bodyExpr)))
              applyAsns = mconcat $ map (snd . exprTranslate Nothing) $ map toApply applies
          in
          -- trace ("outTy = " ++ show outTy) $
          -- MkGuardedExpr cond (asn <> PointsTo Output (Here "__r") (toSuSLikExpr bodyExpr) applyAsns <> tempsAsn)

          -- MkGuardedExpr cond (asn <> AssertEqual "__r" (toSuSLikExpr "" bodyExpr) applyAsns <> tempsAsn)
          MkGuardedExpr cond (asn <> setVar ("__r", resultType) bodyExpr <> applyAsns <> tempsAsn)

      -- -- TODO: Probably should check to see if the expression is *any*
      -- -- base-type expression and do this kind of special case.
      -- --
      -- -- TODO: Should this be a special case?
      -- -- Also, should this use some kind of copy? And should the result
      -- -- name be hard-coded?
      -- MkGuardedExpr cond (asn <> PointsTo Output (Here "__r") (VarS v) Emp)

    guardedTranslate (MkGuardedExpr cond (MkExprWithAsn asn bodyExpr)) =
      let (_, bodyAsn) = exprTranslate Nothing bodyExpr
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

    recName :: RecName
    recName = defName def

    exprTranslate :: Maybe [SuSLikName] -> ElaboratedExpr FsName -> ([SuSLikExpr SuSLikName], Assertion SuSLikName)
    exprTranslate _ (Lower ty _) = absurd ty
    exprTranslate _ (Instantiate _ x _ _) = absurd x
    exprTranslate _ (Var ty v) = (map VarS (loweredParams ty), Emp)
    exprTranslate _ (IntLit i) = ([IntS i], Emp)
    exprTranslate _ (BoolLit b) = ([BoolS b], Emp)

    exprTranslate out (And x y) = combineBin' out AndS x y
    exprTranslate out (Or x y) = combineBin' out OrS x y
    exprTranslate out (Not x) = first (map NotS) $ exprTranslate out x

    exprTranslate out (Add x y) = combineBin' out AddS x y
    exprTranslate out (Sub x y) = combineBin' out SubS x y
    exprTranslate out (Mul x y) = combineBin' out MulS x y

    exprTranslate out (Equal x y) = combineBin' out EqualS x y
    exprTranslate out (Le x y) = combineBin' out LeS x y
    exprTranslate out (Lt x y) = combineBin' out LtS x y

      -- TODO: Are these two correct?
    exprTranslate out (Deref ty x) =
      (map VarS (loweredParams ty), Emp)
    exprTranslate out (Addr ty x) =
      (map VarS (loweredParams ty), Emp)

    exprTranslate out (Apply fName outLayout inLayouts args) =
      let (exprs, asns) = first concat . unzip $ map (exprTranslate (Just $ loweredParams outLayout)) args
          asn = mconcat asns
      in
      (map VarS (loweredParams outLayout),
       HeapletApply (MkLayoutName Nothing fName) (exprs ++ map VarS (loweredParams outLayout)) [] asn)

    exprTranslate out e@(ConstrApply ty@(LayoutParam layoutName) cName args) =
      let (_, asns) = first concat . unzip $ map (exprTranslate (Just $ map ppr $ getParamedNameParams layoutName)) args
          asn = mconcat asns
          layout = lookupLayout layouts (baseLayoutName (getParamedName layoutName))
          -- suslikParams = concatMap getOutParams args
      in

          -- exprs = foldMap toList $ concatMap getOutParams args -- TODO: Generalize this to work with more kinds of expressions
          -- exprs = map toSuSLikExpr args

      -- () <- traceM $ "args = " ++ show args

      let suslikParams = case out of
                            -- Nothing -> genLayoutParams layout
                            Nothing -> map ppr $ getParamedNameParams layoutName
                            Just outVars -> outVars
      in


      let matched = removeHeapletApplies $ applyLayoutExpr layout suslikParams cName $ map (toSuSLikExpr recName) args
      -- let matched = applyLayoutExpr layout suslikParams cName $ map toSuSLikExpr args
      in
      -- let matched = removeHeapletApplies $ applyLayout layout suslikParams cName exprs

      (map VarS suslikParams
            ,asn <> setAssertionMode Output matched
            )


    exprTranslate _ e0@(ConstrApply param _ _) =
      error $ "ill-typed constructor: " ++ show e0 ++ "--> : "++ show param


    combineBin' out op x y = combineBin op (exprTranslate out x) (exprTranslate out y)

combineBin :: (SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr') ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName)
combineBin op (es1, asns1) (es2, asns2) =
  (zipWith op es1 es2, asns1 <> asns2)

getOutParams :: ElaboratedExpr FsName -> [SuSLikExpr SuSLikName]
getOutParams (Var (LayoutParam paramedName) v) =
  map (VarS . ppr) $ getParamedNameParams paramedName
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

getOutParams (Deref ty x) =
  map VarS (loweredParams ty)
getOutParams (Addr ty x) =
  map VarS (loweredParams ty)

getOutParams (Lower ty _) = absurd ty
getOutParams (Instantiate _ x _ _) = absurd x

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

