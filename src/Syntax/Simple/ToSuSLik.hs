--
-- Stage 6 from https://github.com/roboguy13/fun-suslik/blob/d5ccdc275ff13473f8e11af34deb8ce3523f6a9f/README.md
--

{-# LANGUAGE LiberalTypeSynonyms #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Syntax.Simple.ToSuSLik
  (defToSuSLik)
  where


import           Syntax.Simple.Heaplet hiding (Type(..))
import           Syntax.Simple.SuSLik
import           Syntax.Name
import           Syntax.Ppr

import           Data.Foldable
import           Data.List

import qualified Data.Set as Set

import Debug.Trace

fastNub :: Ord a => [a] -> [a]
fastNub = Set.toList . Set.fromList

defToSuSLik :: AsnDef -> InductivePred
defToSuSLik def =
  let (argLowereds, resultLowered) = defType def
      argParams = map toSuSLikParam argLowereds
      -- resultParams = map (`MkSuSLikParam` LocType) $ loweredParams resultLowered
      resultParams = toSuSLikParam resultLowered
      predParams = concat argParams ++ resultParams
      -- predParams = map (`MkSuSLikParam` LocType) argParams
      --                       ++ map (`MkSuSLikParam` LocType) resultParams
  in
  -- trace ("outParams = " ++ show resultParams) $
  MkInductivePred
  { inductivePredName = defName def
  , inductivePredParams = predParams
  , inductivePredBranches = concatMap (toSuSLikBranches (map (map suslikParamName) argParams) (map suslikParamName resultParams)) $ defBranches def
  }
  where
    recName = defName def

    toSuSLikBranches :: [[SuSLikName]] -> [SuSLikName] -> AsnDefBranch -> [SuSLikBranch]
    toSuSLikBranches inParams outParams branch =
        map go $ defBranchGuardeds branch
      where
        patCond = patCondForBranch (zip (defBranchPatterns branch) inParams) outParams branch

        go guarded@(MkGuardedExpr _ rhs) =
          MkSuSLikBranch
            (condForGuarded patCond guarded)
            (toHeapletsRec Nothing (Just recName) rhs)

toSuSLikParam :: ParamTypeP -> [SuSLikParam]
-- toSuSLikParam (PtrParam (Just v) IntBase) = [MkSuSLikParam (ppr v) IntType]
-- toSuSLikParam (PtrParam (Just v) BoolBase) = [MkSuSLikParam (ppr v) BoolType]
toSuSLikParam (PtrParam (Just v) _) = [MkSuSLikParam (ppr v) LocTypeS]
toSuSLikParam (IntParam (Just v)) = [MkSuSLikParam v IntTypeS]
toSuSLikParam (BoolParam (Just v)) = [MkSuSLikParam v BoolTypeS]
toSuSLikParam (IntParam Nothing) = []
toSuSLikParam (BoolParam Nothing) = []
toSuSLikParam (PtrParam Nothing _) = []
toSuSLikParam p@(LayoutParam {}) = map (`MkSuSLikParam` LocTypeS) $ loweredParams p

patCondForBranch :: [(Pattern' a, [SuSLikName])] -> [SuSLikName] -> AsnDefBranch -> SuSLikExpr SuSLikName
patCondForBranch inParams0 outParams branch =
    ands (map varEqZero paramsNotUsed
            ++
          map (NotS . varEqZero) paramsUsed)
  where
    inParams =
      concatMap snd $
      filter (not . isPatternVar . fst) $
      inParams0

    isPatternVar PatternVar{} = True
    isPatternVar _ = False

    paramsNotUsed :: [SuSLikName]
    paramsNotUsed = (fastNub (inParams \\ paramsUsed)) \\ outParams

    paramsUsed :: [SuSLikName]
    paramsUsed =
      (fastNub (concatMap collectParamsAsn (getDefBranchRhs's branch) \\ outParams)
        `intersect` inParams) \\ outParams

    -- removeLayoutApplies Emp = Emp
    -- removeLayoutApplies (PointsTo mode x y rest) = PointsTo mode x y (removeLayoutApplies rest)
    -- removeLayoutApplies (HeapletApply layoutName x y rest)
    --   | layoutNameHasMode layoutName = removeLayoutApplies rest
    --   | otherwise = HeapletApply layoutName x y $ removeLayoutApplies rest
    -- remove

varEqZero :: SuSLikName -> SuSLikExpr SuSLikName
varEqZero n = EqualS (VarS n) (IntS 0)

condForGuarded :: SuSLikExpr SuSLikName -> AsnGuarded -> SuSLikExpr SuSLikName
condForGuarded patCond (MkGuardedExpr cond _) =
  mkAndS patCond (toSuSLikExpr' cond)

collectParams :: AsnDef -> [SuSLikName]
collectParams = concatMap collectParamsAsn . getDefRhs's

collectParamsAsn :: Assertion a -> [a]
collectParamsAsn Emp = []
collectParamsAsn (PointsTo _ lhsLoc _ rest) =
  toList lhsLoc <> collectParamsAsn rest
collectParamsAsn (HeapletApply layoutName suslikParams _ rest)
  | layoutNameHasMode layoutName =
      foldMap toList (toList suslikParams) <> collectParamsAsn rest
  | otherwise = collectParamsAsn rest
collectParamsAsn (Block _ _ rest) = collectParamsAsn rest
collectParamsAsn (TempLoc _ rest) = collectParamsAsn rest
collectParamsAsn (IsNull v) = [v]
collectParamsAsn (Copy _ src _) = [src]
collectParamsAsn (AssertEqual _ _ rest) = collectParamsAsn rest

-- -- | Only for use in translating Boolean conditionals and
-- -- the RHS of points-tos (which should be simplified to basic expressions
-- -- by this stage).
-- toSuSLikExpr' :: (Show ty, Show layoutNameTy) =>
--   ExprX ty layoutNameTy FsName -> SuSLikExpr SuSLikName
-- toSuSLikExpr' (Var _ v) = VarS v
-- toSuSLikExpr' (IntLit i) = IntS i
-- toSuSLikExpr' (BoolLit b) = BoolS b
-- toSuSLikExpr' (And x y) = AndS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' (Or x y) = OrS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' (Not x) = NotS (toSuSLikExpr' x)
-- toSuSLikExpr' (Add x y) = AddS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' (Sub x y) = SubS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' (Mul x y) = MulS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' (Equal x y) = EqualS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' (Le x y) = LeS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' (Lt x y) = LtS (toSuSLikExpr' x) (toSuSLikExpr' y)
-- toSuSLikExpr' e = error $ "toSuSLikExpr': " ++ show e


