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

abstractLayoutBranch :: [SuSLikName] -> [FsName] -> Assertion' FsName -> ScopeLayoutBranchE FsName
abstractLayoutBranch suslikNames fsNames branch =
  abstract (fmap MkParamIndex . (`elemIndex` (suslikNames ++ fsNames))) branch

-- paramIndexToName :: Layout -> [FsName] -> ParamIndex -> SuSLikName
-- paramIndexToName layout fsArgs (MkParamIndex ix) =
--   -- TODO: Does this necessarily work?
--   (layoutSuSLikParams layout ++ fsArgs) !! ix

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

-- type ScopeLayoutBranch = Scope ParamIndex LayoutBranchE

class SubstInjection a b where
  substInject :: a -> b

instance SubstInjection a (Expr a) where
  substInject = Var

instance SubstInjection Name Name where substInject = id
-- instance SubstInjection FsName FsName where substInject = id
-- instance SubstInjection SuSLikName SuSLikName where substInject = id

matchPattern :: Pattern FsName -> ConstrName -> [Expr FsName] -> Maybe PatSubst
matchPattern (MkPattern cName params) cName' args = do
  guard (cName == cName')
  pure (zip params args)

matchBranch :: ConstrName -> [Expr FsName] -> (Pattern FsName, Assertion' FsName) -> Maybe (PatSubst, Assertion' FsName)
matchBranch cName args (pat, branch) = do
  subst <- matchPattern pat cName args
  pure (subst, branch)

-- performSubst :: (Eq a, SubstInjection a b) => Subst a b -> a -> b
-- performSubst subst curr =
--   case lookup curr subst of
--     Just new -> new
--     Nothing -> substInject curr
--
-- applyPatSubstHeaplet :: PatSubst -> Heaplet FsName a -> Heaplet (Expr FsName) a
-- applyPatSubstHeaplet subst (PointsTo ptr tgt) =
--   PointsTo ptr (performSubst subst tgt)
--
-- applyPatSubstHeaplet subst (HeapletApply f suslikArgs fsArg) =
--   HeapletApply f suslikArgs (performSubst subst fsArg)
--
-- applySuSLikSubstHeaplet :: SuSLikSubst -> Heaplet b SuSLikName -> Heaplet b SuSLikName
-- applySuSLikSubstHeaplet subst (PointsTo ptr tgt) =
--   PointsTo (fmap (performSubst subst) ptr) tgt
--
-- applySuSLikSubstHeaplet subst (HeapletApply f suslikArgs fsArg) =
--   HeapletApply f (map (performSubst subst) suslikArgs) fsArg

applyLayout :: Layout -> [Expr SuSLikName] -> ConstrName -> [Expr FsName] -> Assertion' FsName
applyLayout layout suslikArgs cName fsArgs =
  -- case mapScope id (second $ matchBranch cName fsArg) (layoutBranches layout) of
  case mapMaybe (matchBranch cName fsArgs) (layoutBranches layout) of
    [] -> error "applyLayout: Constructor does not match pattern"
    ((subst, branch):_) ->
      let --suslikSubst = zip (layoutSuSLikParams layout) suslikArgs
          branch' = abstractLayoutBranch (layoutSuSLikParams layout) (map fst subst) branch
      in
      -- branch'
      instantiate (MkLayoutBranch . (:[]) . lookupParamIndex layout (suslikArgs ++ fsArgs)) branch'

      -- instantiate (layoutBranchSingle . lookupParamIndex layout fsArgs) branch'

      -- mapScope id (applySuSLikSubstHeaplet suslikSubst . applyPatSubstHeaplet subst) branch
      -- map (applySuSLikSubstHeaplet suslikSubst . applyPatSubstHeaplet subst) branch

-- freshenNotIn :: (Named a, Eq a) => [a] -> a -> NameSupply a
-- freshenNotIn boundVars v
--   | v `elem` boundVars = pure v
--   | otherwise = freshen v

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
applyLayoutMany :: [Layout] -> Layout -> [Expr SuSLikName] -> ConstrName -> [Expr FsName] -> Assertion' FsName --Scope ParamIndex Expr SuSLikName
applyLayoutMany layoutDefs layout0 suslikArgs0 cName0 fsArgs0 = do
  -- let MkLayoutBranch zs = applyLayout layout0 suslikArgs0 cName0 fsArg0

  -- let MkLayoutBranch zs = fromScope $ applyLayout layout0 suslikArgs0 cName0 fsArg0
  let z = applyLayout layout0 suslikArgs0 cName0 fsArgs0

  -- let r = map go zs

  -- let r = _ =<< z
  undefined

  -- MkLayoutBranch $ concatMap getLayoutBranch r
  -- fmap concat $ mapM go zs
  -- fmap concat $ mapM go (applyLayout layout0 suslikArgs0 cName0 fsArg0)
  where
    -- go' :: LayoutBranch a

    go :: Expr FsName -> Assertion' FsName
    go (ExprHeapletApply f suslikArgs (ConstrApply cName fsArgs)) = do
      let nextLayout = lookupLayout layoutDefs f
      undefined
      -- applyLayoutMany layoutDefs nextLayout suslikArgs cName fsArgs
    go heaplet = layoutBranchSingle heaplet

  --   -- go :: Heaplet (Expr FsName) SuSLikName ->
  --   --       [Heaplet (Expr FsName) SuSLikName]
  --   go (ExprHeapletApply f suslikArgs (ConstrApply cName fsArg)) = do
  --     let nextLayout = lookupLayout layoutDefs f
  --     undefined
  --     -- suslikArgs_fresh <- mapM freshen suslikArgs
  --       -- TODO: This might introduce captured variables
  --     -- applyLayoutMany layoutDefs nextLayout suslikArgs_fresh cName fsArg
  --   go heaplet = undefined --pure [heaplet]

-- applyLayoutMany' :: [Layout] -> Layout -> [SuSLikName] -> ConstrName -> [Expr FsName] -> Expr SuSLikName
-- applyLayoutMany' layoutDefs layout suslikArgs cName fsArg =
--   undefined
--   --runNameSupply $ applyLayoutMany layoutDefs layout suslikArgs cName fsArg

