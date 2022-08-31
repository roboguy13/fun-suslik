{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}

module Syntax.Simple.Heaplet
  where

import           Syntax.Name

import           Text.Show.Deriving
import           Data.Functor.Classes
import           Data.Functor.Compose

import           Control.Monad
import           ListT hiding (traverse)

import           GHC.Exts

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

  -- ExprLayoutBranch :: [Heaplet a] -> Expr a

  -- ExprPointsTo :: Loc (Expr a) -> Expr a -> Expr a
  -- ExprHeapletApply :: String -> [Expr a] -> Expr a -> Expr a
  --
  -- ExprLayoutBranch :: Scope ParamIndex LayoutBranchE a -> Expr a

  -- LayoutCaseLambda :: Scope 
  deriving (Functor, Foldable, Traversable)

fsName, suslikName :: String -> Name
fsName = MkName
suslikName = MkName

type LayoutName = String

data Assertion a where
  Emp :: Assertion a
  PointsTo :: Loc a -> a -> Assertion a -> Assertion a
  HeapletApply :: LayoutName -> [a] -> a -> Assertion a -> Assertion a
  deriving (Functor, Show)

type Assertion' a = Assertion (Expr a)

-- exprMap :: (Expr a -> Expr a) -> (Assertion a -> Assertion a)
-- exprMap f = go
--   where
--     go Emp = Emp
--     go (PointsTo x e rest) = PointsTo x (f e) rest
--     go (HeapletApply lName suslikArgs e rest) = 

instance Semigroup (Assertion a) where
  Emp <> b = b
  PointsTo x y rest <> b = PointsTo x y (rest <> b)
  HeapletApply lName suslikArgs e rest <> b = HeapletApply lName suslikArgs e (rest <> b)

instance Monoid (Assertion a) where
  mempty = Emp

maybeToEndo :: (a -> Maybe a) -> (a -> a)
maybeToEndo f x =
  case f x of
    Nothing -> x
    Just y -> y

substLayoutAssertion :: Int -> (Int -> LayoutName -> [Expr FsName] -> Expr FsName -> Maybe (Assertion' FsName)) -> Assertion' FsName -> Assertion' FsName
substLayoutAssertion _level _f Emp = Emp
substLayoutAssertion level f (PointsTo x y rest) = PointsTo x y (substLayoutAssertion level f rest)
substLayoutAssertion level f (HeapletApply lName suslikArgs e rest) =
  case f level lName suslikArgs e of
    Nothing -> HeapletApply lName suslikArgs e (substLayoutAssertion level f rest)
    Just r -> r <> substLayoutAssertion (succ level) f rest

applyLayoutAssertion :: Eq a => [(a, a)] -> [(a, Expr a)] -> Assertion (Expr a) -> Assertion (Expr a)
applyLayoutAssertion suslikSubst fsSubst asn =
  fmap go asn
  where
    go origV@(Var n) =
      case lookup n suslikSubst of
        Just s -> Var s
        Nothing ->
          case lookup n fsSubst of
            Just e -> e
            Nothing -> origV
    go e = e

-- newtype LayoutBranch f a = MkLayoutBranch { getLayoutBranch :: [f a] }
--   deriving (Foldable, Traversable)
--               --ListT Expr
--
-- type LayoutBranchE = LayoutBranch Expr
-- type ScopeLayoutBranchE = Scope ParamIndex LayoutBranchE
--
-- instance IsList (LayoutBranch f a) where
--   type Item (LayoutBranch f a) = f a
--   fromList = MkLayoutBranch
--   toList = getLayoutBranch
--
-- instance Functor f => Functor (LayoutBranch f) where
--   fmap f (MkLayoutBranch xs) = MkLayoutBranch (map (fmap f) xs)
--
-- instance (Monad f, Traversable f) => Applicative (LayoutBranch f) where
--   pure x = MkLayoutBranch [pure x]
--   (<*>) = ap
--
-- instance (Monad f, Traversable f) => Monad (LayoutBranch f) where
--   return = pure
--   MkLayoutBranch xs >>= f = do
--     let zs = concatMap (map join) . fmap sequenceA . fmap (fmap getLayoutBranch) $ map (fmap f) xs
--     MkLayoutBranch zs
--
-- layoutBranchSingle :: Expr a -> LayoutBranchE a
-- layoutBranchSingle e = MkLayoutBranch [e]

type ConstrName = String

instance Applicative Expr where
  pure = Var
  (<*>) = ap

instance Monad Expr where
  return = pure

  Var x >>= f = f x
  IntLit i >>= _ = IntLit i
  BoolLit b >>= _ = BoolLit b

  And x y >>= f = And (x >>= f) (y >>= f)
  Or x y >>= f = Or (x >>= f) (y >>= f)
  Not x >>= f = Not (x >>= f)

  Add x y >>= f = Add (x >>= f) (y >>= f)
  Sub x y >>= f = Sub (x >>= f) (y >>= f)
  Mul x y >>= f = Mul (x >>= f) (y >>= f)

  Equal x y >>= f = Equal (x >>= f) (y >>= f)
  Le x y >>= f = Le (x >>= f) (y >>= f)
  Lt x y >>= f = Lt (x >>= f) (y >>= f)

  Apply fName x >>= f = Apply fName (x >>= f)

  ConstrApply cName args >>= f = ConstrApply cName (map (>>= f) args)

  Lower str x >>= f = Lower str (x >>= f)

  LiftLowerFn l1 l2 x >>= f = LiftLowerFn l1 l2 (x >>= f)

  -- ExprLayoutBranch xs >>= f = do
  --   xs' <- traverse (traverse f) xs
  --   ExprLayoutBranch xs'

  -- ExprPointsTo x y >>= f = do
  --   y' <- fmap f y
  --   let x' = fmap (>>= f) x
  --   ExprPointsTo x' y'
  --
  -- ExprHeapletApply x y z >>= f = do
  --   y' <- traverse (fmap f) y
  --   ExprHeapletApply x y' (z >>= f)


-- data Heaplet a where
--   PointsTo :: Loc a -> a -> Heaplet a
--   HeapletApply :: String -> [a] -> a -> Heaplet a
--   deriving (Show, Functor, Foldable, Traversable)

data Loc a = Here a | a :+ Int
  deriving (Show, Functor, Foldable, Traversable)

instance Applicative Loc where
  pure = Here
  (<*>) = ap

instance Monad Loc where
  return = pure
  Here x >>= f = f x
  (x :+ i) >>= f = f x

{-
data BranchElement a where
  MkBranchElement :: Heaplet a -> BranchElement a
  BranchVar :: a -> BranchElement a -- | Represents an unknown (list of) heaplets using a SuSLikName
  deriving (Show, Functor, Foldable, Traversable)

instance Applicative BranchElement where
  pure = BranchVar
  (<*>) = ap

instance Monad BranchElement where
  return = pure
  BranchVar x >>= f = f x
  MkBranchElement (PointsTo (Here loc) y) >>= f = do
    loc' <- f loc
    y' <- f y
    MkBranchElement (PointsTo (Here loc') y')
  MkBranchElement (PointsTo (x :+ i) y) >>= f = do
    x' <- f x
    y' <- f y
    MkBranchElement (PointsTo (x' :+ i) y')

  MkBranchElement (HeapletApply layoutName xs ys) >>= f = do
    xs' <- mapM f xs
    ys' <- f ys
    MkBranchElement $ HeapletApply layoutName xs' ys'

newtype LayoutBranch a = MkLayoutBranch { getLayoutBranch :: [BranchElement a] }
  deriving (Show, Functor)

instance Applicative LayoutBranch where
  pure x = MkLayoutBranch [pure x]
  (<*>) = ap

instance Monad LayoutBranch where
  return = pure
  -- MkLayoutBranch xs0 >>= f = _ $ map (>>= (map _ . getLayoutBranch)) xs0
  MkLayoutBranch xs0 >>= f =
    let xs' = map (traverse f) xs0
    in
    MkLayoutBranch $ fmap join $ concatMap getLayoutBranch xs'
    -- let xs' = map (_ f) xs0
    -- in
    -- undefined
    -- MkLayoutBranch $ _ $ map (>>= concatMap (getLayoutBranch . _)) xs0

-- instance Applicative (LayoutBranch a) where
--   pure x = MkLayoutBranch [pure x]
--   (<*>) = ap
--
-- instance Monad (LayoutBranch a) where
--   return = pure
--   MkLayoutBranch xs0 >>= f = do
--     let xs0' = concatMap (getLayoutBranch . go) xs0
--
--     MkLayoutBranch xs0'
--     where
--       go (MkBranchElement (PointsTo (Here loc) y)) = do
--         loc' <- f loc
--
--         MkLayoutBranch $ [MkBranchElement (PointsTo (Here loc') y)]
--
--       go (MkBranchElement (HeapletApply layoutName xs ys)) = do
--         xs' <- mapM f xs
--         MkLayoutBranch $ [MkBranchElement (HeapletApply layoutName xs' ys)]
-}

$(deriveShow1 ''Loc)
-- $(deriveShow1 ''Heaplet)
-- $(deriveShow1 ''LayoutBranch)
$(deriveShow1 ''Expr)
-- $(deriveShow1 ''BranchElement)

deriving instance Show a => Show (Expr a)
-- deriving instance (Show (f a), Show a) => Show (LayoutBranch f a)

