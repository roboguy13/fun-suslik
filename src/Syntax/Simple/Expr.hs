{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}

module Syntax.Simple.Expr
  where

import           Data.Void
import           Data.Maybe
import           Data.List

import           Control.Monad
import           Control.Applicative
import           Control.Arrow (first)

import           Syntax.Name

import           Bound

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

data Layout =
  MkLayout
  { layoutName :: String
  , layoutAdtName :: String
  , layoutSuSLikParams :: [SuSLikName]
  , layoutBranches :: [(Pattern FsName, LayoutBranch SuSLikName FsName)]
  }
  deriving (Show)

lookupLayout :: [Layout] -> String -> Layout
lookupLayout layoutDefs name =
  case find ((== name) . layoutName) layoutDefs of
    Nothing -> error $ "lookupLayout: Cannot find layout definition " ++ name
    Just def -> def

type LayoutBranch a b = [Heaplet a b]
type LayoutBranch' = LayoutBranch SuSLikName FsName

data Heaplet a b where
  PointsTo :: Loc a -> b -> Heaplet a b
  HeapletApply :: String -> [a] -> b -> Heaplet a b
  deriving (Show)

data Loc a = Here a | a :+ Int
  deriving (Show, Functor)

type Heaplet' = Heaplet SuSLikName FsName
type ExprHeaplet = Heaplet SuSLikName (Expr FsName)

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

applyPatSubstHeaplet :: PatSubst -> Heaplet a FsName -> Heaplet a (Expr FsName)
applyPatSubstHeaplet subst (PointsTo ptr tgt) =
  PointsTo ptr (performSubst subst tgt)

applyPatSubstHeaplet subst (HeapletApply f suslikArgs fsArg) =
  HeapletApply f suslikArgs (performSubst subst fsArg)

applySuSLikSubstHeaplet :: SuSLikSubst -> Heaplet SuSLikName b -> Heaplet SuSLikName b
applySuSLikSubstHeaplet subst (PointsTo ptr tgt) =
  PointsTo (fmap (performSubst subst) ptr) tgt

applySuSLikSubstHeaplet subst (HeapletApply f suslikArgs fsArg) =
  HeapletApply f (map (performSubst subst) suslikArgs) fsArg

applyLayout :: Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> LayoutBranch SuSLikName (Expr FsName)
applyLayout layout suslikArgs cName fsArg =
  case mapMaybe (matchBranch cName fsArg) (layoutBranches layout) of
    [] -> error "applyLayout: Constructor does not match pattern"
    ((subst, branch):_) ->
      let suslikSubst = zip (layoutSuSLikParams layout) suslikArgs
      in
      map (applySuSLikSubstHeaplet suslikSubst . applyPatSubstHeaplet subst) branch

-- | Apply layout definition enough times to eliminate constructor
-- applications in argument.
applyLayoutMany :: [Layout] -> Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> NameSupply (LayoutBranch SuSLikName (Expr FsName))
applyLayoutMany layoutDefs layout0 suslikArgs0 cName0 fsArg0 =
  fmap concat $ mapM go (applyLayout layout0 suslikArgs0 cName0 fsArg0)
  where
    go :: Heaplet SuSLikName (Expr FsName) ->
          NameSupply [Heaplet SuSLikName (Expr FsName)]
    go (HeapletApply f suslikArgs (ConstrApply cName fsArg)) = do
      let nextLayout = lookupLayout layoutDefs f
      suslikArgs_fresh <- mapM freshen suslikArgs
        -- TODO: This might introduce captured variables
      applyLayoutMany layoutDefs nextLayout suslikArgs_fresh cName fsArg
    go heaplet = pure [heaplet]

applyLayoutMany' :: [Layout] -> Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> LayoutBranch SuSLikName (Expr FsName)
applyLayoutMany' layoutDefs layout suslikArgs cName fsArg =
  runNameSupply $ applyLayoutMany layoutDefs layout suslikArgs cName fsArg


