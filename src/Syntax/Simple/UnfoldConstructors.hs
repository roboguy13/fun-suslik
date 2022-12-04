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

isBaseType :: Named ExprX a -> Bool
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
isBaseType (LetIn _ _v _rhs body) = isBaseType body
isBaseType (IfThenElse _ _ t _) = isBaseType t

getApplies :: Named ExprX a -> FreshGenT (Writer (Assertion SuSLikName)) [(String, ParamTypeP, [ParamTypeP], [Named ExprX a])]
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

    -- traceM $ "assert equal: " ++ show (temp, orig)
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
getApplies (IfThenElse _ c t f) =
  concat <$> mapM getApplies [c, t, f]
getApplies (LetIn _ty _v rhs body) =
  liftA2 (++) (getApplies rhs) (getApplies body)

genTemps :: Named ExprX FsName -> Writer (Assertion FsName) ()
genTemps (Apply fName outLayout inLayouts args) = do
  when (not (isBaseParam outLayout)) $
    forM_ (loweredParams outLayout) $ \x ->
      tell (TempLoc x Emp)

  mapM_ genTemps args

genTemps (Lower ty _) = absurd ty
genTemps (Instantiate _ x _ _) = absurd x
genTemps (Var ty v) = pure ()
genTemps (IntLit i) = pure ()
genTemps (BoolLit b) = pure ()

genTemps (And x y) = genTemps x *> genTemps y
genTemps (Or x y) = genTemps x *> genTemps y
genTemps (Not x) = genTemps x

genTemps (Add x y) = genTemps x *> genTemps y
genTemps (Sub x y) = genTemps x *> genTemps y
genTemps (Mul x y) = genTemps x *> genTemps y

genTemps (Equal x y) = genTemps x *> genTemps y
genTemps (Le x y) = genTemps x *> genTemps y
genTemps (Lt x y) = genTemps x *> genTemps y

genTemps (Deref ty x) = genTemps x
genTemps (Addr ty x) = genTemps x

genTemps (LetIn ty v rhs body) =
  genTemps rhs *> genTemps body

genTemps (IfThenElse ty c t f) =
  genTemps c *> genTemps t *> genTemps f

genTemps (ConstrApply ty cName args) =
  mapM_ genTemps args


setVar :: (SuSLikName, ParamTypeP) -> Named ExprX FsName -> Assertion FsName
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
    outVars = loweredParams resultType
    [outVar] = outVars

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
          MkGuardedExpr cond (asn <> setVar (outVar, resultType) bodyExpr <> applyAsns <> tempsAsn)

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

    exprTranslate :: Maybe [SuSLikName] -> Named ExprX FsName -> ([SuSLikExpr SuSLikName], Assertion SuSLikName)
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

    exprTranslate out (LetIn ty v rhs body) =
      let (es1, asn1) = exprTranslate out rhs
          (es2, asn2) = exprTranslate out body
      in
      (es1 <> es2, asn1 <> asn2)

    exprTranslate out (IfThenElse ty c t f) =
      combineTri' out IteS c t f

    exprTranslate out (Apply fName outLayout inLayouts args) =
      let asnTemps = execWriter $ mapM genTemps args

          (exprs, asns) = first concat . unzip $ map (exprTranslate (Just $ loweredParams outLayout)) args
          asn = mconcat asns
      in
      (map VarS (loweredParams outLayout),
       HeapletApply (MkLayoutName Nothing fName) (exprs ++ map VarS (loweredParams outLayout)) [] asn <> asnTemps)

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


      let matched = removeHeapletApplies (getParamedName layoutName) $ applyLayoutExpr layout suslikParams cName $ map (toSuSLikExpr recName) args
      -- let matched = applyLayoutExpr layout suslikParams cName $ map toSuSLikExpr args
      in
      -- let matched = removeHeapletApplies $ applyLayout layout suslikParams cName exprs

      (map VarS suslikParams
            ,asn <> setAssertionMode Output matched
            )


    exprTranslate _ e0@(ConstrApply param _ _) =
      error $ "ill-typed constructor: " ++ show e0 ++ "--> : "++ show param


    combineBin' out op x y = combineBin op (exprTranslate out x) (exprTranslate out y)
    combineTri' out op x y z = combineTri op (exprTranslate out x) (exprTranslate out y) (exprTranslate out z)

combineBin :: (SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr') ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName)
combineBin op (es1, asns1) (es2, asns2) =
  (zipWith op es1 es2, asns1 <> asns2)

combineTri :: (SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr' -> SuSLikExpr') ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName) ->
  ([SuSLikExpr SuSLikName], Assertion SuSLikName)
combineTri op (es1, asns1) (es2, asns2) (es3, asns3) =
  (zipWith3 op es1 es2 es3, asns1 <> asns2 <> asns3)

genLayoutParams :: Layout -> FreshGen [String]
genLayoutParams layout =
  mapM (getFreshWith . ("__y_" <>)) $ layoutSuSLikParams layout

-- -- | Equality constraints to connect the expression output variables to the
-- -- output parameters
-- genOutputEqualities :: [SuSLikName] -> Named ExprX a -> Assertion SuSLikName
-- genOutputEqualities 

