{-# LANGUAGE GADTs #-}

module Syntax.Simple.SuSLik
  where

import           Syntax.Simple.Expr
import           Syntax.Name

data InductivePred =
  MkInductivePred
  { inductivePredName :: String
  , inductivePredParams :: [SuSLikParam]
  , inductivePredBranches :: [SuSLikBranch]
  }
  deriving (Show)

data SuSLikParam =
  MkSuSLikParam
  { suslikParamName :: SuSLikName
  , suslikParamType :: SuSLikType
  }
  deriving (Show)

-- NOTE: For now, does not support pure part
data SuSLikBranch =
  MkSuSLikBranch
  { suslikBranchCond :: SuSLikExpr
  , suslikBranchRhs :: [SuSLikHeaplet]
  }
  deriving (Show)

data SuSLikExpr where
  IntS :: Int -> SuSLikExpr
  BoolS :: Bool -> SuSLikExpr

  AndS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr
  OrS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr
  NotS :: SuSLikExpr -> SuSLikExpr

  LtS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr
  LeS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr
  EqualS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr

  AddS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr
  SubS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr
  MulS :: SuSLikExpr -> SuSLikExpr -> SuSLikExpr
  deriving (Show)

data SuSLikType = IntType | LocType | BoolType | SetType
  deriving (Show)

