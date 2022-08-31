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
import           Control.Arrow (first, second)

import           Syntax.Name
import           Syntax.Ppr

import           Bound
import           Bound.Scope

import           Syntax.Simple.Heaplet

import           ListT (fromFoldable)


data Pattern a = MkPattern ConstrName [FsName]
  deriving (Show)

-- instance Ppr a => Ppr (Expr a) where
--   ppr (Var v) = ppr v
--   ppr (IntLit i) = show i
--   ppr (BoolLit b) = show b
--   ppr (And x y) = pprBinOp "&&" x y
--   ppr (Or x y) = pprBinOp "||" x y
--   ppr (Not x) = "not (" <> ppr x <> ")"
--   ppr (Add x y) = pprBinOp "+" x y
--   ppr (Sub x y) = pprBinOp "-" x y
--   ppr (Mul x y) = pprBinOp "*" x y
--   ppr (Equal x y) = pprBinOp "==" x y
--   ppr (Le x y) = pprBinOp "<=" x y
--   ppr (Lt x y) = pprBinOp "<" x y
--   -- TODO: Finish

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
  , layoutBranches :: [(Pattern FsName, Assertion' FsName)]
  }
  deriving (Show)

mkLayout :: String -> String -> [SuSLikName] -> [(Pattern FsName, Assertion' FsName)] -> Layout
mkLayout name adtName suslikParams branches =
  MkLayout
    { layoutName = name
    , layoutAdtName = adtName
    , layoutSuSLikParams = suslikParams
    , layoutBranches = branches
    }
  where
    -- go :: LayoutBranch FsName -> Scope ParamIndex LayoutBranch SuSLikName
    -- go branch = abstract (fmap MkParamIndex . (`elemIndex` suslikParams)) branch

-- paramIndexToName :: Layout -> [FsName] -> ParamIndex -> SuSLikName
-- paramIndexToName layout fsArgs (MkParamIndex ix) =
--   -- TODO: Does this necessarily work?
--   (layoutSuSLikParams layout ++ fsArgs) !! ix

matchPattern :: Pattern FsName -> ConstrName -> [Expr FsName] -> Maybe PatSubst
matchPattern (MkPattern cName params) cName' args = do
  guard (cName == cName')
  pure (zip params args)

matchBranch :: ConstrName -> [Expr FsName] -> (Pattern FsName, Assertion' FsName) -> Maybe (PatSubst, Assertion' FsName)
matchBranch cName args (pat, branch) = do
  subst <- matchPattern pat cName args
  pure (subst, branch)

getMatchingBranch :: Layout -> ConstrName -> [Expr FsName] -> Maybe (PatSubst, Assertion' FsName)
getMatchingBranch layout cName fsArgs =
  foldr (<|>) Nothing (map (matchBranch cName fsArgs) (layoutBranches layout))

lookupParamIndex :: Layout -> [Expr FsName] -> ParamIndex -> Expr FsName
lookupParamIndex layout fsArgs (MkParamIndex ix0) =
  go (layoutSuSLikParams layout) ix0
  where
    go (x:_) 0 = Var x
    go (_:xs) i = go xs (i-1)
    go [] i = fsArgs !! i

nameToParamIndex :: Layout -> SuSLikName -> ParamIndex
nameToParamIndex layout name =
  case name `elemIndex` layoutSuSLikParams layout of
    Nothing -> error $ "nameToParamIndex: Cannot find the following name in parameter list: " ++ show name
    Just ix -> MkParamIndex ix

lookupLayout :: [Layout] -> String -> Layout
lookupLayout layoutDefs name =
  case find ((== name) . layoutName) layoutDefs of
    Nothing -> error $ "lookupLayout: Cannot find layout definition " ++ name
    Just def -> def

type Subst a b = [(a, b)]
type PatSubst = Subst FsName (Expr FsName)
type SuSLikSubst = Subst SuSLikName SuSLikName

applyLayout :: Int -> Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> Assertion' FsName
applyLayout level layout suslikArgs cName fsArgs =
  case getMatchingBranch layout cName fsArgs of
    Nothing -> error $ "applyLayout: Cannot find branch for constructor " ++ cName
    Just (fsSubst, asn) ->
      let suslikSubst = zip (layoutSuSLikParams layout) suslikArgs
      in
      applyLayoutAssertion suslikSubst fsSubst (fmap (fmap (setNameIndex level)) asn)

getVar :: Expr a -> a
getVar (Var v) = v
getVar _ = error "getVar"

getLayoutSubstFn :: Int -> Layout -> (LayoutName -> [Expr FsName] -> Expr FsName -> Maybe (Assertion' FsName))
getLayoutSubstFn level layout lName suslikArgs (ConstrApply cName xs) = do
  guard (layoutName layout == lName)
  Just $ applyLayout level layout (map getVar suslikArgs) cName xs
getLayoutSubstFn _ _ _ _ _ = Nothing

getLayoutsSubstFn :: [Layout] -> Int -> (LayoutName -> [Expr FsName] -> Expr FsName -> Maybe (Assertion' FsName))
getLayoutsSubstFn layouts level lName suslikArgs fsArg =
  foldr (<|>) Nothing $ map (\layout -> getLayoutSubstFn level layout lName suslikArgs fsArg) layouts

unfoldLayoutDefs :: Int -> [Layout] -> Assertion' FsName -> Assertion' FsName
unfoldLayoutDefs level defs asn =
  substLayoutAssertion level (getLayoutsSubstFn defs) asn

-- | Apply layout definition enough times to eliminate constructor
-- applications in argument.
applyLayoutMany :: [Layout] -> Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> Assertion' FsName
applyLayoutMany layoutDefs layout0 suslikArgs0 cName0 fsArgs0 = do
  undefined

