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

defToSuSLik :: [LoweredType] -> ConcreteType -> AsnDef -> InductivePred
defToSuSLik inTypes outType def = undefined
  -- MkInductivePred
  -- { inductivePredName = defName def
  -- , inductivePredParams = params
  -- }
  -- where
  --   params = collectParams def

concreteTypeToSuSLik :: ConcreteType -> SuSLikType
concreteTypeToSuSLik IntConcrete = IntType
concreteTypeToSuSLik BoolConcrete = BoolType
concreteTypeToSuSLik LayoutConcrete{} = LocType


-- | NOTE: Do not provide output parameters. Only input parameters
patCondForBranch :: [SuSLikName] -> AsnDefBranch -> SuSLikExpr SuSLikName
patCondForBranch params branch =
    ands (map varEqZero paramsNotUsed
            ++
          map (NotS . varEqZero) paramsUsed)
  where
    paramsNotUsed :: [SuSLikName]
    paramsNotUsed = params \\ paramsUsed

    paramsUsed :: [SuSLikName]
    paramsUsed = concatMap collectParamsAsn $ getDefBranchRhs's branch

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

-- | Only for use in translating Boolean conditionals
toSuSLikExpr :: Expr FsName -> SuSLikExpr SuSLikName
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


