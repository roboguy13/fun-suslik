{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}

module Nucleus.Expr where

import           Bound

import           Data.List
import           Data.Maybe

import           Data.Data

import           Control.Monad
import           Control.Applicative

import           Data.Functor.Classes
import           Data.Deriving (deriveShow1, deriveEq1, deriveOrd1, deriveEq)

import           Data.Void
import           Data.List.NonEmpty (NonEmpty (..))

import           Data.Bifunctor.TH
import           Data.Bifunctor

import           Unsafe.Coerce

import           EGraph.EGraph
import           EGraph.Rewrite
import           Representation.Parts
import           Backend.DOT

infixr 0 :->
data Type a where
  (:->) :: Type a -> Type a -> Type a
  TyVar :: a -> Type a

  BoolType :: Type a
  IntType :: Type a
  ListType :: Type a -> Type a

  UnitType :: Type a

  PairType :: Type a -> Type a -> Type a

  Refinement :: a -> Type a -> [ExprEq Void a] -> Type a

data ExprEq uv a = WrappedExpr uv a :=: WrappedExpr uv a
  deriving (Show, Eq, Ord)

deriving instance Ord a => Eq (Type a)
deriving instance Ord a => Ord (Type a)

-- | Hack to get around limitations caused by the TH stage restriction
data WrappedExpr uv a =
  WrappedExpr
    (ExprU uv a)
    (forall uvX x. (Eq uvX, Eq x) => ExprU uvX x -> ExprU uvX x -> Bool)
    (forall uvX x. (Ord uvX, Ord x) => ExprU uvX x -> ExprU uvX x -> Ordering)
    (forall uvX x. (Show uvX, Show x) => ExprU uvX x -> String)

instance (Eq uv, Eq a) => Eq (WrappedExpr uv a) where
  WrappedExpr x eq _ _ == WrappedExpr y _ _ _ = eq x y
instance (Ord uv, Ord a) => Ord (WrappedExpr uv a) where
  compare (WrappedExpr x _ comp _) (WrappedExpr y _ _ _) = comp x y
instance (Show uv, Show a) => Show (WrappedExpr uv a) where
  show (WrappedExpr x _ _ showIt) = showIt x

unwrapExpr :: WrappedExpr uv a -> ExprU uv a
unwrapExpr (WrappedExpr e _ _ _) = e

infixl 0 :@
data ExprU uv a where
  UVar :: uv -> ExprU uv a
  Var :: a -> ExprU uv a
  IntLit :: Int -> ExprU uv a
  BoolLit :: Bool -> ExprU uv a

  Add :: ExprU uv a -> ExprU uv a -> ExprU uv a
  Sub :: ExprU uv a -> ExprU uv a -> ExprU uv a
  Mul :: ExprU uv a -> ExprU uv a -> ExprU uv a

  (:@) :: ExprU uv a -> ExprU uv a -> ExprU uv a
  Lam :: Scope () (ExprU uv) a -> ExprU uv a

    -- Non-recursive
  Let :: ExprU uv a -> Scope () (ExprU uv) a -> ExprU uv a

  Ann :: Type Void -> ExprU uv a -> ExprU uv a

  Comb :: Combinator -> ExprU uv a

pattern Apply f x = f :@ x

type Expr = ExprU Void


data Combinator
  =
    ConstF
  | ComposeF
  -- * Lists
  --   - Constructors
  | Nil | Cons
  --   - Accessors
  | Head | Tail
  --   - Folds
  | Foldr | Scanr

  --   - Misc derived
  | Map
  | Sum

  -- * Pairs
  --   - CCC product operations
  | Pair | Dup
  | Fst | Snd
  | Swap | PairJoin

  | Unit

  | IfThenElse

  | Le
  | IntEq

  | Not
  | And
  | Or
  deriving (Show, Eq, Ord)

type Env a = [(a, Expr a)]

deriveShow1 ''ExprU

deriving instance Functor (ExprU uv)
deriving instance Foldable (ExprU uv)
deriving instance Traversable (ExprU uv)

deriving instance (Show uv, Show a) => Show (ExprU uv a)

deriving instance Show a => Show (Type a)


instance Applicative (ExprU uv) where
  pure = Var
  (<*>) = ap

instance Monad (ExprU uv) where
  return = Var

  UVar x >>= _ = UVar x
  Var x >>= f = f x

  IntLit i >>= _ = IntLit i
  BoolLit b >>= _ = BoolLit b

  Add x y >>= f = Add (x >>= f) (y >>= f)
  Sub x y >>= f = Sub (x >>= f) (y >>= f)
  Mul x y >>= f = Mul (x >>= f) (y >>= f)

  (x :@ y) >>= f = (x >>= f) :@ (y >>= f)
  Lam e >>= f = Lam (e >>>= f)
  Let rhs body >>= f =
    Let (rhs >>= f) (body >>>= f)

  Ann ty e >>= f = Ann ty (e >>= f)
  Comb c >>= _ = Comb c


$(deriveEq1 ''ExprU)
-- deriveEq1 ''Type
deriveOrd1 ''ExprU

-- instance Eq1 Type

-- deriving instance Eq a => Eq (Type a)
deriving instance (Eq uv, Eq a) => Eq (ExprU uv a)
--
deriving instance (Ord uv, Ord a) => Ord (ExprU uv a)
--
-- deriving instance (Typeable a) => Typeable (Type a)
-- deriving instance (Data a) => Data (Type a)
--
-- deriving instance Typeable Combinator
-- deriving instance Data Combinator
--
-- deriving instance (Typeable uv, Typeable a) => Typeable (ExprU uv a)
-- deriving instance (Data uv, Data a) => Data (ExprU uv a)
--
-- instance TreeNode (ExprU uv a) where
--   nodeChildren (Var {}) = []
--   nodeChildren (IntLit {}) = []
--   nodeChildren (BoolLit {}) = []
--
--   nodeChildren (Add x y) = [x, y]
--   nodeChildren (Sub x y) = [x, y]
--   nodeChildren (Mul x y) = [x, y]
--
--   nodeChildren (Apply f x) = [f, x]
--
--     -- TODO: Should be able to go into the body for these?
--   nodeChildren (Lam {}) = []
--   nodeChildren (Let {}) = []
--
--   nodeChildren (Ann _ty e) = [e]
--   nodeChildren (Comb {}) = []

wrappedExpr :: ExprU uv a -> WrappedExpr uv a
wrappedExpr e = WrappedExpr e (==) compare show

instance (Data uv, Data a, Ord uv, Ord a) => GraphNode (ExprU uv a) where
  -- nodeCost e = 1 + sum (map nodeCost (partsChildren e))
  nodeCost e = 1 + sum (map nodeCost (nodeChildren e))

instance Unify ExprU where
  isUVar (UVar x) = Just x
  isUVar _ = Nothing
  anyUVar x = unsafeCoerce x
  anyUVar' x = unsafeCoerce x

binaryOp :: (a -> a -> b) -> NonEmpty a -> b
binaryOp f (x :| [y]) = f x y

unaryOp :: (a -> b) -> NonEmpty a -> b
unaryOp f (x :| []) = f x

binaryParts :: ToParts a => a -> a -> (a -> a -> a) -> Parts a
binaryParts x y f = Parts (fmap toParts (x :| [y])) (binaryOp f)

unaryParts :: ToParts a => a -> (a -> a) -> Parts a
unaryParts x f = Parts (fmap toParts (x :| [])) (unaryOp f)

instance ToParts (ExprU uv a) where
  toParts e@(UVar _) = Leaf e
  toParts e@(Var _) = Leaf e
  toParts e@(IntLit _) = Leaf e
  toParts e@(BoolLit _) = Leaf e

  toParts (Add x y) = binaryParts x y Add
  toParts (Sub x y) = binaryParts x y Sub
  toParts (Mul x y) = binaryParts x y Mul

  toParts (Apply x y) = binaryParts x y Apply

    -- TODO: Should we descend into these? If so, how?
  toParts e@(Lam {}) = Leaf e
  toParts e@(Let {}) = Leaf e

  toParts (Ann ty e) = unaryParts e (Ann ty)

-- instance Unify ExprU

-- | Top-level definition
data Def =
  Def
    { defType :: Type String
    , defBinding :: (String, [String], Expr String)
    }

deriving instance Show Def

data TopLevel
  = TopLevelDef Def
  | Theorem (ExprEq Void String) -- Can also function as a rewrite

getDef :: TopLevel -> Maybe Def
getDef (TopLevelDef d) = Just d
getDef _ = Nothing

lam :: Eq a => a -> Expr a -> Expr a
lam x = Lam . abstract1 x

mkLams :: Eq a => [a] -> Expr a -> Expr a
mkLams [] body = body
mkLams (arg:args) body = lam arg (mkLams args body)

test1 :: Expr ()
test1 = Add (Mul (IntLit 5) (IntLit 1)) (Mul (IntLit 10) (IntLit 2))

test2 :: Expr ()
test2 = test1 `Mul` IntLit 1

reverseTest :: Def
reverseTest =
  Def
  { defType =
      Refinement "rev" (ListType IntType :-> ListType IntType)
        [ wrappedExpr (Var "rev" :@ Var "xs") :=: wrappedExpr (Var "rev" :@ (Var "rev" :@ Var "xs"))
        , wrappedExpr (Var "append" :@ (Var "rev" :@ Var "ys") :@ (Var "rev" :@ Var "xs"))
            :=:
          wrappedExpr (Var "rev" :@ (Var "append" :@ Var "xs" :@ Var "ys"))
        ] :: Type String
  , defBinding = ("reverse", ["xs"], undefined :: Expr String)
  }

defToExprAssoc :: Def -> (String, Expr String)
defToExprAssoc (Def ty (name, params, body)) = (name, mkLams params body)

rewrite1 :: Rewrite ExprU String ()
rewrite1 = toParts (Mul (UVar "?x") (IntLit 1)) :=> toParts (UVar "?x")

stepPair :: (Eq a, Show a) => Env a -> Expr a -> Expr a -> Maybe (Expr a, Expr a)
stepPair env x y = do
  let x'_maybe = step env x
      y'_maybe =
        case x'_maybe of
          Nothing -> step env y
          Just {} -> Just y

      x' = fromMaybe x x'_maybe
      y' = fromMaybe y y'_maybe

  x'_maybe <|> y'_maybe

  pure (x', y')

stepApplyPair :: (Eq a, Show a) => Env a -> (Expr a -> Expr a -> r) -> Expr a -> Expr a -> Maybe r
stepApplyPair env f x y = uncurry f <$> stepPair env x y

class Fresh a where
  fresh :: Env a -> a

step :: (Eq a, Show a) => Env a -> Expr a -> Maybe (Expr a)
step env (Var v) =
  case lookup v env of
    Nothing -> error $ "No such binding " ++ show v
    Just e -> Just e

step _env (IntLit _) = Nothing
step _env (BoolLit _) = Nothing

step env (Add (IntLit x) (IntLit y)) = Just $ IntLit (x + y)
step env (Sub (IntLit x) (IntLit y)) = Just $ IntLit (x - y)
step env (Mul (IntLit x) (IntLit y)) = Just $ IntLit (x * y)

step env (Add x y) = stepApplyPair env Add x y
step env (Sub x y) = stepApplyPair env Sub x y
step env (Mul x y) = stepApplyPair env Mul x y

step env (Apply (Lam scoped) x) =
  Just $ instantiate1 x scoped

step env (Comb ConstF :@ x :@ y) = Just y
step env (Comb ComposeF :@ f :@ g :@ x) = Just (f :@ (g :@ x))
step env (Comb Nil) = Nothing
step env (Comb Head :@ (Comb Cons :@ x :@ xs)) = Just x
step env (Comb Tail :@ (Comb Cons :@ x :@ xs)) = Just xs
step env (Comb Foldr :@ f :@ z :@ (Comb Cons :@ x :@ xs)) =
  Just (f :@ x :@ (Comb Foldr :@ f :@ z :@ xs))

step env (Comb Le :@ IntLit x :@ IntLit y) = Just (BoolLit (x <= y))
step env (Comb Le :@ BoolLit x :@ BoolLit y) = Just (BoolLit (x <= y))
step env (Comb IntEq :@ IntLit x :@ IntLit y) = Just (BoolLit (x == y))

step env (Comb Not :@ BoolLit b) = Just (BoolLit (not b))
step env (Comb And :@ BoolLit x :@ BoolLit y) = Just (BoolLit (x && y))
step env (Comb Or :@ BoolLit x :@ BoolLit y) = Just (BoolLit (x || y))

step env (Comb Map :@ _ :@ Comb Nil) = Just $ Comb Nil
step env (Comb Map :@ f :@ (Comb Cons :@ x :@ xs)) = Just (Comb Cons :@ (f :@ x) :@ (Comb Map :@ f :@ xs))

step env (Comb Sum :@ Comb Nil) = Just $ IntLit 0
step env (Comb Sum :@ (Comb Cons :@ x :@ xs)) = Just (Add x (Comb Sum :@ xs))

-- step env (Comb Scanr :@ f :@ z :@ (Comb Cons :@ x :@ xs)) =
--   let v = fresh env
--   in
--   Let (
--   Comb Cons :@ 

  -- Non-strict evaluation order
step env (Apply f arg) = stepApplyPair env Apply f arg

step env (Lam _) = Nothing

step env (Let rhs body) = Just $ instantiate1 rhs body

step env (Ann {}) = Nothing
step env (Comb {}) = Nothing

stepN :: (Eq a, Show a) => Int -> Env a -> Expr a -> Maybe (Expr a)
stepN 0    _env e = Just e
stepN fuel env  e  = step env e >>= stepN (fuel-1) env

step1 :: (Eq a, Show a) => Env a -> Expr a -> Maybe (Expr a)
step1 = stepN 1

eval :: (Eq a, Show a) => Env a -> Expr a -> Expr a
eval env e0 =
  case step1 env e0 of
    Nothing -> e0
    Just e' -> eval env e'

