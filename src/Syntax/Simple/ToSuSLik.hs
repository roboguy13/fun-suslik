--
-- Stage 6 from https://github.com/roboguy13/fun-suslik/blob/d5ccdc275ff13473f8e11af34deb8ce3523f6a9f/README.md
--

{-# LANGUAGE LiberalTypeSynonyms #-}

module Syntax.Simple.ToSuSLik
  (defToSuSLik)
  where


import           Syntax.Simple.Heaplet hiding (Type(..))
import           Syntax.Simple.SuSLik
import           Syntax.Name

import           Data.Foldable
import           Data.List

import qualified Data.Set as Set

fastNub :: Ord a => [a] -> [a]
fastNub = Set.toList . Set.fromList

defToSuSLik :: AsnDef -> InductivePred
defToSuSLik def =
  let (argLowereds, resultLowered) = defType def
      argParams = concatMap loweredParams argLowereds
      resultParams = loweredParams resultLowered
      predParams = argParams ++ resultParams
      -- predParams = map (`MkSuSLikParam` LocType) argParams
      --                       ++ map (`MkSuSLikParam` LocType) resultParams
  in
  MkInductivePred
  { inductivePredName = defName def
  , inductivePredParams = map (`MkSuSLikParam` LocType) predParams
  , inductivePredBranches = concatMap (toSuSLikBranches predParams resultParams) $ defBranches def
  }

concreteTypeToSuSLik :: ConcreteType -> SuSLikType
concreteTypeToSuSLik IntConcrete = IntType
concreteTypeToSuSLik BoolConcrete = BoolType
concreteTypeToSuSLik LayoutConcrete{} = LocType

toSuSLikBranches :: [SuSLikName] -> [SuSLikName] -> AsnDefBranch -> [SuSLikBranch]
toSuSLikBranches inParams outParams branch =
    map go $ defBranchGuardeds branch
  where
    patCond = patCondForBranch inParams outParams branch

    go guarded@(MkGuardedExpr _ rhs) =
      MkSuSLikBranch
        (condForGuarded patCond guarded)
        (toHeaplets rhs)

toHeaplets :: Assertion FsName -> [Heaplet SuSLikName]
toHeaplets Emp = []
toHeaplets (PointsTo mode x y rest) =
  PointsToS (modeToMutability mode) x (toSuSLikExpr y) : toHeaplets rest
toHeaplets (HeapletApply lName suslikArgs _es rest) =
  HeapletApplyS (genLayoutName lName) suslikArgs : toHeaplets rest

patCondForBranch :: [SuSLikName] -> [SuSLikName] -> AsnDefBranch -> SuSLikExpr SuSLikName
patCondForBranch inParams outParams branch =
    ands (map varEqZero paramsNotUsed
            ++
          map (NotS . varEqZero) paramsUsed)
  where
    paramsNotUsed :: [SuSLikName]
    paramsNotUsed = (fastNub (inParams \\ paramsUsed)) \\ outParams

    paramsUsed :: [SuSLikName]
    paramsUsed =
      fastNub (concatMap collectParamsAsn (getDefBranchRhs's branch))
        `intersect` inParams

varEqZero :: SuSLikName -> SuSLikExpr SuSLikName
varEqZero n = EqualS (VarS n) (IntS 0)

condForGuarded :: SuSLikExpr SuSLikName -> AsnGuarded -> SuSLikExpr SuSLikName
condForGuarded patCond (MkGuardedExpr cond _) =
  mkAndS patCond (toSuSLikExpr cond)

collectParams :: AsnDef -> [SuSLikName]
collectParams = concatMap collectParamsAsn . getDefRhs's

collectParamsAsn :: Assertion a -> [a]
collectParamsAsn Emp = []
collectParamsAsn (PointsTo _ lhsLoc _ rest) =
  toList lhsLoc <> collectParamsAsn rest
collectParamsAsn (HeapletApply _ _ _ rest) = collectParamsAsn rest

-- | Only for use in translating Boolean conditionals and
-- the RHS of points-tos (which should be simplified to basic expressions
-- by this stage).
toSuSLikExpr :: (Show ty, Show layoutNameTy) =>
  ExprX ty layoutNameTy FsName -> SuSLikExpr SuSLikName
toSuSLikExpr (Var _ v) = VarS v
toSuSLikExpr (IntLit i) = IntS i
toSuSLikExpr (BoolLit b) = BoolS b
toSuSLikExpr (And x y) = AndS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Or x y) = OrS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Not x) = NotS (toSuSLikExpr x)
toSuSLikExpr (Add x y) = AddS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Sub x y) = SubS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Mul x y) = MulS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Equal x y) = EqualS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Le x y) = LeS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Lt x y) = LtS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr e = error $ "toSuSLikExpr: " ++ show e


