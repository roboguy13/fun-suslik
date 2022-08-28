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
  { suslikBranchCond :: SuSLikExpr SuSLikName
  , suslikBranchRhs :: [SuSLikHeaplet]
  }
  deriving (Show)

data SuSLikExpr a where
  VarS :: a -> SuSLikExpr a
  IntS :: Int -> SuSLikExpr a
  BoolS :: Bool -> SuSLikExpr a

  AndS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  OrS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  NotS :: SuSLikExpr a -> SuSLikExpr a

  LtS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  LeS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  EqualS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a

  AddS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  SubS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  MulS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  deriving (Show)

data SuSLikType = IntType | LocType | BoolType | SetType
  deriving (Show)

