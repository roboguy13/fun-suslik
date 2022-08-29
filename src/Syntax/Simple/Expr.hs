{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax.Simple.Expr
  where

import           Data.Void
import           Data.Maybe
import           Data.List

import           Control.Monad
import           Control.Applicative
import           Control.Arrow (first)

import           Syntax.Name
import           Syntax.Ppr

import           Bound

import           Syntax.Simple.Heaplet

type ConstrName = String

data Pattern a = MkPattern ConstrName [FsName]
  deriving (Show)

data Expr a where
  Var :: a -> Expr a

  IntLit :: Int -> Expr a
  BoolLit :: Bool -> Expr a

  And :: Expr a -> Expr a -> Expr a
  Or :: Expr a -> Expr a -> Expr a
  Not :: Expr a -> Expr a

  Add :: Expr a -> Expr a -> Expr a
  Sub :: Expr a -> Expr a -> Expr a
  Mul :: Expr a -> Expr a -> Expr a

  Equal :: Expr a -> Expr a -> Expr a
  Le :: Expr a -> Expr a -> Expr a
  Lt :: Expr a -> Expr a -> Expr a

  Apply :: String -> Expr a -> Expr a

  ConstrApply :: ConstrName -> [Expr a] -> Expr a

  Lower :: String -> Expr a -> Expr a

    -- | Represents @lower L_1 . f . lift L_2@
  LiftLowerFn ::
    String -> -- | L_1
    String -> -- | L_2
    Expr a -> -- | f
    Expr a
  deriving (Show)

pprBinOp :: (Ppr a, Ppr b) => String -> a -> b -> String
pprBinOp op x y = "(" <> ppr x <> " " <> op <> " " <> ppr y <> ")"

instance Ppr a => Ppr (Expr a) where
  ppr (Var v) = ppr v
  ppr (IntLit i) = show i
  ppr (BoolLit b) = show b
  ppr (And x y) = pprBinOp "&&" x y
  ppr (Or x y) = pprBinOp "||" x y
  ppr (Not x) = "not (" <> ppr x <> ")"
  ppr (Add x y) = pprBinOp "+" x y
  ppr (Sub x y) = pprBinOp "-" x y
  ppr (Mul x y) = pprBinOp "*" x y
  ppr (Equal x y) = pprBinOp "==" x y
  ppr (Le x y) = pprBinOp "<=" x y
  ppr (Lt x y) = pprBinOp "<" x y
  -- TODO: Finish

type ClosedExpr = Expr Void

data Type where
  IntType :: Type
  BoolType :: Type

  FnType :: Type -> Type -> Type

  AdtType :: Adt -> Type
  LayoutType :: Layout -> Type
  deriving (Show)

data Adt =
  MkAdt
  { adtName :: String
  , adtBranches :: [AdtBranch]
  }
  deriving (Show)

data AdtBranch =
  MkAdtBranch
  { adtBranchConstr :: ConstrName
  , adtBranchFields :: [Type]
  }
  deriving (Show)

newtype ParamIndex = MkParamIndex Int
  deriving (Show, Eq, Ord, Enum)

data Layout =
  MkLayout
  { layoutName :: String
  , layoutAdtName :: String
  , layoutSuSLikParams :: [SuSLikName]
  , layoutBranches :: [(Pattern FsName, Scope ParamIndex (LayoutBranch FsName) SuSLikName)]
  }
  deriving (Show)

lookupLayout :: [Layout] -> String -> Layout
lookupLayout layoutDefs name =
  case find ((== name) . layoutName) layoutDefs of
    Nothing -> error $ "lookupLayout: Cannot find layout definition " ++ name
    Just def -> def

instance (Ppr a, Ppr b) => Ppr (Heaplet a b) where
  ppr (PointsTo x y) = ppr x <> " :-> " <> ppr y

  -- TODO: Is this correct?
  ppr (HeapletApply f suslikArgs fsArg) =
    f <> "(" <> intercalate ", " (map ppr suslikArgs) <> ")"

instance Ppr a => Ppr (Loc a) where
  ppr (Here x) = ppr x
  ppr (x :+ i) = "(" <> ppr x <> "+" <> show i <> ")"

instance (Ppr a, Ppr b) => Ppr [Heaplet a b] where
  ppr xs = intercalate " ** " (map ppr xs)

type Heaplet' = Heaplet FsName SuSLikName
type ExprHeaplet = Heaplet (Expr FsName) SuSLikName

type SuSLikHeaplet = Heaplet SuSLikName SuSLikName

type Subst a b = [(a, b)]
type PatSubst = Subst FsName (Expr FsName)
type SuSLikSubst = Subst SuSLikName SuSLikName

class SubstInjection a b where
  substInject :: a -> b

instance SubstInjection a (Expr a) where
  substInject = Var

instance SubstInjection FsName FsName where substInject = id
instance SubstInjection SuSLikName SuSLikName where substInject = id

matchPattern :: Pattern FsName -> ConstrName -> [Expr FsName] -> Maybe PatSubst
matchPattern (MkPattern cName params) cName' args = do
  guard (cName == cName')
  pure (zip params args)

matchBranch :: ConstrName -> [Expr FsName] -> (Pattern FsName, LayoutBranch') -> Maybe (PatSubst, LayoutBranch')
matchBranch cName args (pat, branch) = do
  subst <- matchPattern pat cName args
  pure (subst, branch)

performSubst :: (Eq a, SubstInjection a b) => Subst a b -> a -> b
performSubst subst curr =
  case lookup curr subst of
    Just new -> new
    Nothing -> substInject curr

applyPatSubstHeaplet :: PatSubst -> Heaplet FsName a -> Heaplet (Expr FsName) a
applyPatSubstHeaplet subst (PointsTo ptr tgt) =
  PointsTo ptr (performSubst subst tgt)

applyPatSubstHeaplet subst (HeapletApply f suslikArgs fsArg) =
  HeapletApply f suslikArgs (performSubst subst fsArg)

applySuSLikSubstHeaplet :: SuSLikSubst -> Heaplet b SuSLikName -> Heaplet b SuSLikName
applySuSLikSubstHeaplet subst (PointsTo ptr tgt) =
  PointsTo (fmap (performSubst subst) ptr) tgt

applySuSLikSubstHeaplet subst (HeapletApply f suslikArgs fsArg) =
  HeapletApply f (map (performSubst subst) suslikArgs) fsArg

applyLayout :: Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> LayoutBranch (Expr FsName) SuSLikName
applyLayout layout suslikArgs cName fsArg =
  case mapMaybe (matchBranch cName fsArg) (layoutBranches layout) of
    [] -> error "applyLayout: Constructor does not match pattern"
    ((subst, branch):_) ->
      let suslikSubst = zip (layoutSuSLikParams layout) suslikArgs
      in
      map (applySuSLikSubstHeaplet suslikSubst . applyPatSubstHeaplet subst) branch

freshenNotIn :: (Named a, Eq a) => [a] -> a -> NameSupply a
freshenNotIn boundVars v
  | v `elem` boundVars = pure v
  | otherwise = freshen v

-- -- TODO: This needs to use simultaneous (uniform) substitutions
-- freshenFVs :: (Named a, Eq a) =>
--   [a] -> LayoutBranch a b -> NameSupply (LayoutBranch a b)
-- freshenFVs boundVars = mapM go
--   where
--     go (PointsTo x y) = do
--       x' <- mapM (freshenNotIn boundVars) x
--       pure $ PointsTo x' y
--     go (HeapletApply f suslikArgs fsArg) = undefined

-- | Apply layout definition enough times to eliminate constructor
-- applications in argument.
applyLayoutMany :: [Layout] -> Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> NameSupply (LayoutBranch (Expr FsName) SuSLikName)
applyLayoutMany layoutDefs layout0 suslikArgs0 cName0 fsArg0 =
  fmap concat $ mapM go (applyLayout layout0 suslikArgs0 cName0 fsArg0)
  where
    go :: Heaplet (Expr FsName) SuSLikName ->
          NameSupply [Heaplet (Expr FsName) SuSLikName]
    go (HeapletApply f suslikArgs (ConstrApply cName fsArg)) = do
      let nextLayout = lookupLayout layoutDefs f
      suslikArgs_fresh <- mapM freshen suslikArgs
        -- TODO: This might introduce captured variables
      applyLayoutMany layoutDefs nextLayout suslikArgs_fresh cName fsArg
    go heaplet = pure [heaplet]

applyLayoutMany' :: [Layout] -> Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> LayoutBranch (Expr FsName) SuSLikName
applyLayoutMany' layoutDefs layout suslikArgs cName fsArg =
  runNameSupply $ applyLayoutMany layoutDefs layout suslikArgs cName fsArg


