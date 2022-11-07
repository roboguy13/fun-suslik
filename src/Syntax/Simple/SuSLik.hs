{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax.Simple.SuSLik
  where

-- import           Syntax.Simple.Expr
import           Syntax.Simple.Heaplet hiding (Type(..))
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
    ,"{ ?? }"
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

data PointsToMutability = Unrestricted | ReadOnly | Temp
  deriving (Show)

modeToMutability :: Mode -> PointsToMutability
modeToMutability Input = ReadOnly
modeToMutability Output = Unrestricted

data Heaplet a where
  PointsToS :: PointsToMutability -> Loc a -> SuSLikExpr a -> Heaplet a
  HeapletApplyS :: String -> [SuSLikExpr a] -> Heaplet a
  BlockS :: a -> Int -> Heaplet a
  Func :: String -> [SuSLikExpr a] -> SuSLikExpr a -> Heaplet a
  deriving (Show, Functor)

pointsToSymbol :: PointsToMutability -> String
pointsToSymbol Unrestricted = ":->"
pointsToSymbol ReadOnly = ":=>"
pointsToSymbol Temp = ":~>"

pattern PointsToS' x y = PointsToS ReadOnly x y

instance Ppr a => Ppr (Heaplet a) where
  ppr (PointsToS mut x y) = unwords [ppr x, pointsToSymbol mut, ppr y]

  ppr (HeapletApplyS f args) = f ++ "(" ++ intercalate ", " (map ppr args) ++ ")"
  ppr (BlockS x i) = "[" ++ ppr x ++ "," ++ show i ++ "]"

  ppr (Func f args result) = "func " ++ f ++ "(" ++ intercalate ", " (map ppr (args ++ [result])) ++ ")"

instance Ppr a => Ppr [Heaplet a] where
  ppr [] = "emp"
  ppr xs = intercalate " ** " $ map ppr xs

data SuSLikType = IntType | LocType | BoolType | SetType
  deriving (Show)

