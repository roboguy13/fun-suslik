{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

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
import           Syntax.FreshGen
import           Syntax.Simple.SuSLik

import           Bound
import           Bound.Scope

import           Syntax.Simple.Heaplet

import           Data.Either

import           GHC.Stack

import Debug.Trace

data Pattern a = MkPattern ConstrName [FsName]
  deriving (Show)

getPatternVars :: Pattern a -> [FsName]
getPatternVars (MkPattern _ vs) = vs

getPatternConstr :: Pattern a -> ConstrName
getPatternConstr (MkPattern cName _) = cName

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

isVar :: Expr a -> Bool
isVar (Var x) = True
isVar _ = False

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

applyLayoutPattern :: Layout -> [SuSLikName] -> Pattern FsName -> Assertion' FsName
applyLayoutPattern layout suslikArgs (MkPattern cName args) =
    removeAppsLayout $ applyLayout 0 layout suslikArgs cName (map Var args)

getVar :: (Ppr a, HasCallStack) => Expr a -> a
getVar (Var v) = v
getVar e = error $ "getVar: " ++ ppr e

getLayoutSubstFn :: Int -> Layout -> (LayoutName -> [Expr FsName] -> Expr FsName -> Maybe (Assertion' FsName))
getLayoutSubstFn level layout lName suslikArgs (ConstrApply cName xs) = do
  guard (layoutName layout == lName)
  Just $ applyLayout level layout (map getVar suslikArgs) cName xs
getLayoutSubstFn _ _ _ _ _ = Nothing

getLayoutsSubstFn :: [Layout] -> Int -> (LayoutName -> [Expr FsName] -> Expr FsName -> Maybe (Assertion' FsName))
getLayoutsSubstFn layouts level lName suslikArgs fsArg =
  foldr (<|>) Nothing $ map (\layout -> getLayoutSubstFn level layout lName suslikArgs fsArg) layouts

unfoldLayoutDefsAt :: Int -> [Layout] -> Assertion' FsName -> Assertion' FsName
unfoldLayoutDefsAt level defs asn =
  substLayoutAssertion level (getLayoutsSubstFn defs) asn

-- | Unfold layout definitions until there are no more constructor
-- applications in a layout application
unfoldLayoutDefs :: [Layout] -> Assertion' FsName -> Assertion' FsName
unfoldLayoutDefs defs = go 1
  where
    go level x
      | not (hasConstrApp x) = x
      | otherwise            = go (succ level) (unfoldLayoutDefsAt level defs x)

hasConstrApp :: Assertion' FsName -> Bool
hasConstrApp Emp = False
hasConstrApp (PointsTo _ _ rest) = hasConstrApp rest
hasConstrApp (HeapletApply _ _ (ConstrApply {}) rest) = True
hasConstrApp (HeapletApply _ _ _ rest) = hasConstrApp rest

-- -- | Connect with (potentially) an intermediate variable
-- connect :: 

-- | Turn "L[x...] (f y...)" into "lower L [x...] (f y...)" then reduce using
-- the Haskell 'lower'
toLowers :: HasCallStack => [Layout] -> Assertion' FsName -> FreshGen (Assertion' FsName)
toLowers defs = go
  where
    go :: Assertion' FsName -> FreshGen (Assertion' FsName)
    go Emp = pure Emp
    go (PointsTo x y rest) = PointsTo x y <$> (go rest)
    go (HeapletApply layoutName suslikParams e rest) = do
      lower defs (lookupLayout defs layoutName) (map getVar suslikParams) e >>= \case
        Left {} -> error $ "toLowers: " ++ ppr e
        Right asn -> fmap (asn <>) (go rest)

-- | Turn "x :-> (f e)" into "x :-> y, f[y] e"
pointsToIntermediate :: Assertion' FsName -> FreshGen (Assertion' FsName)
pointsToIntermediate = go
  where
    go :: Assertion' FsName -> FreshGen (Assertion' FsName)
    go Emp = pure Emp
    go (PointsTo x (Apply f e) rest) = do
      v <- getFresh
      r <- go rest
      pure $ PointsTo x (Var v) (HeapletApply f [Var v] e r)
    go (PointsTo x y rest) = PointsTo x y <$> go rest
    go (HeapletApply f suslikParams e rest) =
      HeapletApply f suslikParams e <$> go rest

toSuSLikExpr :: Expr a -> Maybe (SuSLikExpr a)
toSuSLikExpr (Var v) = Just $ VarS v
toSuSLikExpr (IntLit i) = Just $ IntS i
toSuSLikExpr (BoolLit b) = Just $ BoolS b
toSuSLikExpr (And x y) = liftA2 AndS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Or x y) = liftA2 OrS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Not x) = fmap NotS (toSuSLikExpr x)

toSuSLikExpr (Lt x y) = liftA2 LtS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Le x y) = liftA2 LeS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Equal x y) = liftA2 EqualS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Add x y) = liftA2 AddS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Sub x y) = liftA2 SubS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Mul x y) = liftA2 MulS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr e = Nothing

toSuSLikExpr_unsafe :: (HasCallStack, Ppr a) => Expr a -> SuSLikExpr a
toSuSLikExpr_unsafe e =
  case toSuSLikExpr e of
    Just s -> s
    Nothing -> error $ "toSuSLikExpr_unsafe: " ++ ppr e

-- | Remove applications from layout expansion
removeAppsLayout :: Assertion' FsName -> Assertion' FsName
removeAppsLayout Emp = Emp
removeAppsLayout (PointsTo x y rest) = PointsTo x y (removeAppsLayout rest)
removeAppsLayout (HeapletApply _ _ _ rest) = removeAppsLayout rest

lower' :: HasCallStack => [Layout] -> Layout -> [SuSLikName] -> Expr FsName -> Assertion' FsName
lower' defs layout suslikArgs e =
  case runFreshGen (lower defs layout suslikArgs e) of
    (_, Right x) -> x
    _ -> error "lower'"

lower :: HasCallStack => [Layout] -> Layout -> [SuSLikName] -> Expr FsName -> FreshGen (Either (SuSLikExpr FsName) (Assertion' FsName))
lower defs layout suslikArgs = go 0
  where
    go :: Int -> Expr FsName -> FreshGen (Either (SuSLikExpr FsName) (Assertion' FsName))
    go level (Var v) = pure $ Left (VarS v)
    go level (IntLit i) = pure $ Left (IntS i)
    go level (BoolLit b) = pure $ Left (BoolS b)
    go level (And x y) = lowerBinOp level "&&" AndS x y
    go level (Or x y) = lowerBinOp level "||" OrS x y
    go level (Not x) = do
      x_E <- go level x
      case x_E of
        Left x' -> pure $ Left $ NotS x'
        _ -> error "lower: Expected expression argument to 'not'"

    go level (Lt x y) = lowerBinOp level "<" LtS x y
    go level (Le x y) = lowerBinOp level "<=" LeS x y
    go level (Equal x y) = lowerBinOp level "==" EqualS x y
    go level (Add x y) = lowerBinOp level "+" AddS x y
    go level (Sub x y) = lowerBinOp level "-" SubS x y
    go level (Mul x y) = lowerBinOp level "*" MulS x y

    go level (ConstrApply cName args) = do
      let suslikParams = suslikArgs --layoutSuSLikParams layout
          -- suslikParam = head suslikParams -- TODO: Use all the parameters for this

      loweredArgs <- mapM (go level) args
      let level' = maximum $ fmap maximum $ fmap (fmap maxUniq) $ rights loweredArgs
      let asn0 = applyLayout (succ level) layout suslikParams cName args
      asn <- pointsToIntermediate asn0

      -- trace ("asn = " ++ ppr asn) $
      pure $ Right asn

      -- pure $ Right $ toLowers defs asn

      -- pure $ Right $ applyLayout

    -- go level (Apply f (Apply g arg)) = undefined
    go level (Apply f arg) = pure . Right $ HeapletApply f (map Var suslikArgs) arg Emp

    lowerBinOp ::
      Int -> String -> (SuSLikExpr FsName -> SuSLikExpr FsName -> SuSLikExpr FsName)
      -> Expr FsName -> Expr FsName -> FreshGen (Either (SuSLikExpr FsName) (Assertion' FsName))
    lowerBinOp level name f x y = do
      x_E <- go level x
      y_E <- go level y
      case (x_E, y_E) of
        (Left x', Left y') -> pure $ Left $ f x' y'
        _ -> error $ "lowerBinOp: Expected expression argument to " ++ name

