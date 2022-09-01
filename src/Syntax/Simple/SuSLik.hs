{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module Syntax.Simple.SuSLik
  where

-- import           Syntax.Simple.Expr
import           Syntax.Simple.Heaplet
import           Syntax.Name
import           Syntax.Ppr

import           Data.List

data InductivePred =
  MkInductivePred
  { inductivePredName :: String
  , inductivePredParams :: [SuSLikParam]
  , inductivePredBranches :: [SuSLikBranch]
  }
  deriving (Show)

instance Ppr InductivePred where
  ppr (MkInductivePred name params branches) =
    unlines'
    ["predicate " <> name <> "(" <> intercalate ", " (map ppr params) <> ") {"
    ,unlines' (map (\x -> "| " ++ ppr x) branches)
    ,"}"
    ]

unlines' = intercalate "\n"

data SuSLikSig =
  MkSuSLikSig
  { suslikSigName :: String
  , suslikSigParams :: [SuSLikParam]
  , suslikSigPre :: [Heaplet String]
  , suslikSigPost :: [Heaplet String]
  }

instance Ppr SuSLikSig where
  ppr (MkSuSLikSig name params pre post) =
    unlines
    ["void " <> name <> "(" <> intercalate ", " (map ppr params) <> ")"
    ,"  { " <> ppr pre <> " }"
    ,"  { " <> ppr post <> " }"
    ]

data SuSLikParam =
  MkSuSLikParam
  { suslikParamName :: String
  , suslikParamType :: SuSLikType
  }
  deriving (Show)

instance Ppr SuSLikParam where
  ppr (MkSuSLikParam name ty) = unwords [ppr ty, ppr name]

instance Ppr SuSLikType where
  ppr IntType = "int"
  ppr BoolType = "bool"
  ppr SetType = "set"
  ppr LocType = "loc"

locParam :: String -> SuSLikParam
locParam n = MkSuSLikParam n LocType

-- NOTE: For now, does not support pure part
data SuSLikBranch =
  MkSuSLikBranch
  { suslikBranchCond :: SuSLikExpr SuSLikName
  , suslikBranchRhs :: [Heaplet SuSLikName]
  }
  deriving (Show)

instance Ppr SuSLikBranch where
  ppr (MkSuSLikBranch cond rhs) = unwords [ppr cond, "=>", "{", ppr rhs, "}"]

data Heaplet a where
  PointsToS :: Loc a -> SuSLikExpr a -> Heaplet a
  HeapletApplyS :: String -> [SuSLikExpr a] -> Heaplet a
  deriving (Show, Functor)

instance Ppr a => Ppr (Heaplet a) where
  ppr (PointsToS x y) = unwords [ppr x, ":->", ppr y]
  ppr (HeapletApplyS f args) = f ++ "(" ++ intercalate ", " (map ppr args) ++ ")"

instance Ppr a => Ppr [Heaplet a] where
  ppr [] = "emp"
  ppr xs = intercalate " ** " $ map ppr xs

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
  deriving (Show, Functor)

mkAndS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
mkAndS (BoolS True) y = y
mkAndS x (BoolS True) = x
mkAndS x y = AndS x y

instance Ppr a => Ppr (SuSLikExpr a) where
  ppr (VarS v) = ppr v
  ppr (IntS i) = show i
  ppr (BoolS True) = "true"
  ppr (BoolS False) = "false"

  ppr (AndS x y) = pprBinOp "&&" x y
  ppr (OrS x y) = pprBinOp "||" x y
  ppr (NotS x) = "(not " ++ ppr x ++ ")"

  ppr (AddS x y) = pprBinOp "+" x y
  ppr (SubS x y) = pprBinOp "-" x y
  ppr (MulS x y) = pprBinOp "*" x y

  ppr (EqualS x y) = pprBinOp "==" x y
  ppr (LeS x y) = pprBinOp "<=" x y
  ppr (LtS x y) = pprBinOp "<" x y

data SuSLikType = IntType | LocType | BoolType | SetType
  deriving (Show)

