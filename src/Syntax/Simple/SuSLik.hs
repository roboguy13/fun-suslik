{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Syntax.Simple.SuSLik
  where

-- import           Syntax.Simple.Expr
import           Syntax.Simple.Heaplet hiding (Type(..))
import           Syntax.Name
import           Syntax.Ppr

import           Data.List

import           Data.Data
import           Data.Data.Lens
import           Control.Lens (universe)

data InductivePred =
  MkInductivePred
  { inductivePredName :: String
  , inductivePredParams :: [SuSLikParam]
  , inductivePredBranches :: [SuSLikBranch]
  }
  deriving (Show, Data)

instance Size InductivePred where
  size (MkInductivePred n xs ys) = 2 + sum (map size xs) + sum (map size ys)

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
  , suslikSigPre :: SuSLikAssertion String
  , suslikSigPost :: SuSLikAssertion String
  } deriving (Data)

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
  deriving (Show, Data)

instance Size SuSLikParam where
  size (MkSuSLikParam n ty) = 2 + size ty

instance Ppr SuSLikParam where
  ppr (MkSuSLikParam name ty) = unwords [ppr ty, ppr name]

instance Ppr SuSLikType where
  ppr IntTypeS = "int"
  ppr BoolTypeS = "bool"
  ppr SetTypeS = "set"
  ppr LocTypeS = "loc"

locParam :: String -> SuSLikParam
locParam n = MkSuSLikParam n LocTypeS

-- NOTE: For now, does not support pure part
data SuSLikBranch =
  MkSuSLikBranch
  { suslikBranchCond :: SuSLikExpr SuSLikName
  , suslikBranchRhs :: SuSLikAssertion SuSLikName
  }
  deriving (Show, Data)

instance Size SuSLikBranch where
  size (MkSuSLikBranch lhs rhs) = 1 + size lhs + size rhs

instance Ppr SuSLikBranch where
  ppr (MkSuSLikBranch cond rhs) = unwords [ppr cond, "=>", "{", ppr rhs, "}"]

data PointsToMutability = Unrestricted | ReadOnly | Temp
  deriving (Show, Data)

modeToMutability :: Mode -> PointsToMutability
modeToMutability Input = ReadOnly
modeToMutability Output = Unrestricted

data Heaplet a where
  PointsToS :: PointsToMutability -> Loc a -> SuSLikExpr a -> Heaplet a
  HeapletApplyS :: String -> [SuSLikExpr a] -> Heaplet a
  BlockS :: a -> Int -> Heaplet a
  TempLocS :: a -> Heaplet a
  -- FuncS :: String -> [SuSLikExpr a] -> SuSLikExpr a -> Heaplet a
  FuncS :: String -> [SuSLikExpr a] -> Heaplet a
  deriving (Show, Functor, Data)

instance Data a => Size (Heaplet a) where
  size (PointsToS mut loc e) = 2 + size loc + size e
  size (HeapletApplyS n xs) = 2 + sum (map size xs)
  size (BlockS x i) = 3
  size (TempLocS i) = 2
  size (FuncS s xs) = 2 + sum (map size xs)

data SuSLikAssertion a where
  CopyS :: String -> a -> a -> SuSLikAssertion a
  IsNullS :: a -> SuSLikAssertion a
  Heaplets :: [Equality a] -> [Heaplet a] -> SuSLikAssertion a
  deriving (Show, Functor, Data)

data Equality a = MkEquality (Loc a) (SuSLikExpr a)
  deriving (Show, Functor, Data)

instance Data a => Size (Equality a) where
  size (MkEquality loc e) = 1 + size loc + size e

instance Data a => Size (SuSLikAssertion a) where
  size (CopyS x y z) = 3
  size (IsNullS x) = 2
  size (Heaplets xs ys) = 1 + sum (map size xs) + sum (map size ys)

instance Semigroup (SuSLikAssertion a) where
  Heaplets [] [] <> y = y
  x <> Heaplets [] [] = x

  Heaplets xs ys <> Heaplets xs' ys' = Heaplets (xs <> xs') (ys <> ys')

  IsNullS {} <> _ = error "Cannot combine IsNullS with another SuSLikAssertion"
  _ <> IsNullS {} = error "Cannot combine IsNullS with another SuSLikAssertion"

  CopyS {} <> _ = error "Cannot combine CopyS with another SuSLikAssertion"
  _ <> CopyS {} = error "Cannot combine CopyS with another SuSLikAssertion"

instance Monoid (SuSLikAssertion a) where
  mempty = Heaplets [] []

asnCons :: Heaplet a -> SuSLikAssertion a -> SuSLikAssertion a
asnCons h asn = Heaplets [] [h] <> asn

eqCons :: Equality a -> SuSLikAssertion a -> SuSLikAssertion a
eqCons eq asn = Heaplets [eq] [] <> asn

pointsToSymbol :: PointsToMutability -> String
pointsToSymbol Unrestricted = ":->"
pointsToSymbol ReadOnly = ":=>"
pointsToSymbol Temp = ":~>"

pattern PointsToS' x y = PointsToS ReadOnly x y

instance Ppr a => Ppr (Heaplet a) where
  ppr (PointsToS mut x y) = unwords [ppr x, pointsToSymbol mut, ppr y]

  ppr (HeapletApplyS f args) = f ++ "(" ++ intercalate ", " (map ppr args) ++ ")"
  ppr (BlockS x i) = "[" ++ ppr x ++ "," ++ show i ++ "]"

  ppr (FuncS f args) = "func " ++ f ++ "(" ++ intercalate ", " (map ppr args) ++ ")"
  ppr (TempLocS v) = "temploc " ++ ppr v

-- instance Ppr a => Ppr [Heaplet a] where
--   ppr [] = "emp"
--   ppr xs = intercalate " ** " $ map ppr xs

instance Ppr a => Ppr (SuSLikAssertion a) where
  ppr (CopyS lName src dest) = "func " <> lName <> "__copy(" <> ppr src <> ", " <> ppr dest <> ")"
  ppr (IsNullS v) = ppr v <> " == null ; emp"
  ppr (Heaplets [] []) = "emp"
  ppr (Heaplets [] xs) = intercalate " ** " $ map ppr xs
  ppr (Heaplets eqs xs) = ppr eqs <> " ; " <> ppr (Heaplets [] xs)

instance Ppr a => Ppr (Equality a) where
  ppr (MkEquality x y) = ppr x <> " == " <> ppr y

instance Ppr a => Ppr [Equality a] where
  ppr [] = "true"
  ppr [x] = ppr x
  ppr (x:xs) = ppr x <> " && " <> ppr xs

data SuSLikType = IntTypeS | LocTypeS | BoolTypeS | SetTypeS
  deriving (Show, Data)

instance Size SuSLikType where
  size IntTypeS = 1
  size LocTypeS = 1
  size BoolTypeS = 1
  size SetTypeS = 1

toHeapletsRec :: Maybe String -> Assertion FsName -> SuSLikAssertion SuSLikName
toHeapletsRec recName_maybe = go
  where
    go Emp = mempty
    go (PointsTo mode x (FnOutVar y) rest) =
      eqCons (MkEquality x (VarS y)) $ go rest

    go (PointsTo mode x y rest) =
        -- TODO: This always uses the "standard" (writable) mode. Is this
        -- correct?
      asnCons (PointsToS Unrestricted x y) (go rest)

      -- asnCons (PointsToS (modeToMutability mode) x y)
      --         (go rest)
    go (HeapletApply lName suslikArgs _es rest)
      | Just recName <- recName_maybe
      , genLayoutName lName == recName || layoutNameHasMode lName =
          asnCons (HeapletApplyS (genLayoutName lName) suslikArgs)
                  (go rest)
      | Just{} <- recName_maybe =
          asnCons (FuncS (genLayoutName lName) suslikArgs)
                  (go rest)
      | otherwise =
          asnCons (HeapletApplyS (genLayoutName lName) suslikArgs)
                  (go rest)
    go (Block v sz rest) =
      asnCons (BlockS v sz)
              (go rest)
    go (TempLoc v rest) =
      asnCons (TempLocS v)
              (go rest)
    go (IsNull v) = IsNullS v
    go (Copy lName src dest) = CopyS lName src dest
    go (AssertEqual lhs rhs rest) =
      eqCons (MkEquality (Here lhs) rhs) (go rest)

layoutCond :: [SuSLikName] -> Assertion FsName -> SuSLikExpr FsName
layoutCond [] _ = BoolS True
layoutCond predParams asn =
  foldr1 AndS (map (NotS . isZero) usedParams ++ map isZero otherParams)
  where
    isZero n = VarS n `EqualS` IntS 0
    usedParams = filter isUsed predParams
    otherParams = predParams \\ usedParams

    asnLocs = pointsLocs asn

    isUsed p = p `elem` map getLocBase asnLocs

data Spec a =
  MkSpec
    { specFnName :: String
    , specParams :: [(SuSLikType, String)]
    , specPre :: [Heaplet a]
    , specPost :: [Heaplet a]
    }
  deriving (Show, Data)

instance Ppr a => Ppr (Spec a) where
  ppr (MkSpec fnName params pre post) =
    unlines
      [ "void " <> fnName <> "(" <> intercalate ", " (map (\(ty, x) -> unwords [ppr ty, ppr x]) params) <> ")"
      , "  { " <> intercalate " ** " (map ppr pre) <> " }"
      , "  { " <> intercalate " ** " (map ppr post) <> " }"
      , "{ ?? }"
      ]

instance Data a => Size (Spec a) where
  size (MkSpec _ params pre post) = 2 + (2*length params) + sum (map size pre) + sum (map size post)

