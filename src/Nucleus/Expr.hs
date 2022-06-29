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

-- {-# OPTIONS -Wincomplete-patterns #-}

module Nucleus.Expr where

import           Bound
import           Bound.Scope

import           Data.List
import           Data.Maybe
import           Data.Char

import           Data.Data
import           Data.Foldable

import           Control.Monad
import           Control.Applicative

import           Data.Functor.Classes
import           Data.Deriving

import           Data.Void
import           Data.List.NonEmpty (NonEmpty (..))

import           Data.Bifunctor.TH
import           Data.Bifunctor

import           Unsafe.Coerce

import           EGraph.EGraph
import           EGraph.Rewrite
import           Representation.Parts
import           Backend.DOT

import           Text.Megaparsec (PosState (..))

deriving instance Ord a => Ord (PosState a)

data SrcLocKind = InSrc | InferredAt
  deriving (Eq, Ord, Show)

type SrcOffset = Int

data SrcSpan = SrcSpan' SrcOffset SrcOffset
  deriving (Eq, Ord, Show)

pattern SrcSpan x y = SrcLoc InSrc (SrcSpan' x y)

data SrcLoc = NoSrcLoc | SrcLoc SrcLocKind SrcSpan
  deriving (Eq, Ord, Show)

setSrcLocKind :: SrcLocKind -> SrcLoc -> SrcLoc
setSrcLocKind _ NoSrcLoc = NoSrcLoc
setSrcLocKind kind (SrcLoc _ pos) = SrcLoc kind pos

class HasSrcLoc a where
  getSrcLoc :: a -> SrcLoc
  removeSrcLoc :: a -> a

instance HasSrcLoc SrcLoc where
  getSrcLoc = id
  removeSrcLoc = const NoSrcLoc

infixr 0 :->
data Type a where
  Arr :: SrcLoc -> Type a -> Type a -> Type a
  TyVar :: SrcLoc -> a -> Type a

  BoolType :: SrcLoc -> Type a
  IntType :: SrcLoc -> Type a
  ListType :: SrcLoc -> Type a -> Type a

  UnitType :: SrcLoc -> Type a

  PairType :: SrcLoc -> Type a -> Type a -> Type a

  Refinement :: SrcLoc -> a -> Type a -> [ExprEq Void a] -> Type a

instance HasSrcLoc (Type a) where
  getSrcLoc (Arr srcLoc _ _) = srcLoc
  getSrcLoc (TyVar srcLoc x) = srcLoc
  getSrcLoc (BoolType srcLoc) = srcLoc
  getSrcLoc (IntType srcLoc) = srcLoc
  getSrcLoc (ListType srcLoc a) = srcLoc
  getSrcLoc (UnitType srcLoc) = srcLoc
  getSrcLoc (PairType srcLoc a b) = srcLoc
  getSrcLoc (Refinement srcLoc v ty eqs) = srcLoc

  removeSrcLoc (Arr _ x y) =
    Arr NoSrcLoc (removeSrcLoc x) (removeSrcLoc y)
  removeSrcLoc (TyVar _ x) = TyVar NoSrcLoc x
  removeSrcLoc (BoolType _) = BoolType NoSrcLoc
  removeSrcLoc (IntType _) = IntType NoSrcLoc
  removeSrcLoc (ListType _ a) = ListType NoSrcLoc (removeSrcLoc a)
  removeSrcLoc (UnitType _) = UnitType NoSrcLoc
  removeSrcLoc (PairType _ a b) =
    PairType NoSrcLoc (removeSrcLoc a) (removeSrcLoc b)
  removeSrcLoc (Refinement _ v ty eqs) =
    Refinement NoSrcLoc v (removeSrcLoc ty) (map removeSrcLoc eqs)

pattern a :-> b <- Arr _ a b where
  a :-> b = Arr NoSrcLoc a b

a .-> b = Arr NoSrcLoc a b

data ExprEq uv a = WrappedExpr uv a :=: WrappedExpr uv a
  deriving (Show, Eq, Ord)

instance HasSrcLoc (ExprEq uv a) where
  getSrcLoc (x :=: _) = getSrcLoc x
  removeSrcLoc (x :=: y) =
    removeSrcLoc x :=: removeSrcLoc y


deriving instance (Ord a) => Eq (Type a)
deriving instance (Ord a) => Ord (Type a)

-- deriving instance Functor Type

-- | Hack to get around limitations caused by the TH stage restriction
data WrappedExpr uv a =
  WrappedExpr
    (ExprU uv a)
    (forall uvZ z. (Eq uvZ, Eq z) => ExprU uvZ z -> ExprU uvZ z -> Bool)
    (forall uvZ z. (Ord uvZ, Ord z) => ExprU uvZ z -> ExprU uvZ z -> Ordering)
    (forall uvZ z. (Show uvZ, Show z) => ExprU uvZ z -> String)
    (forall uvZ z. ExprU uvZ z -> SrcLoc)
    (forall uvZ z. ExprU uvZ z -> ExprU uvZ z)


instance (Eq uv, Eq a) => Eq (WrappedExpr uv a) where
  WrappedExpr x eq _ _ _ _ == WrappedExpr y _ _ _ _ _ = eq x y
instance (Ord uv, Ord a) => Ord (WrappedExpr uv a) where
  compare (WrappedExpr x _ comp _ _ _) (WrappedExpr y _ _ _ _ _) = comp x y
instance (Show uv, Show a) => Show (WrappedExpr uv a) where
  show (WrappedExpr x _ _ showIt _ _) = showIt x
instance HasSrcLoc (WrappedExpr uv a) where
  getSrcLoc (WrappedExpr x _ _ _ f _) = f x
  removeSrcLoc (WrappedExpr x eq ord showIt f g) =
    WrappedExpr (g x) eq ord showIt f g

unwrapExpr :: WrappedExpr uv a -> ExprU uv a
unwrapExpr (WrappedExpr e _ _ _ _ _) = e

data ExprU uv a where
  UVar :: SrcLoc -> uv -> ExprU uv a
  Var :: SrcLoc -> a -> ExprU uv a
  IntLit :: SrcLoc -> Int -> ExprU uv a
  BoolLit :: SrcLoc -> Bool -> ExprU uv a

  Add :: SrcLoc -> ExprU uv a -> ExprU uv a -> ExprU uv a
  Sub :: SrcLoc -> ExprU uv a -> ExprU uv a -> ExprU uv a
  Mul :: SrcLoc -> ExprU uv a -> ExprU uv a -> ExprU uv a

  Apply :: SrcLoc -> ExprU uv a -> ExprU uv a -> ExprU uv a
  Lam :: SrcLoc -> String -> Scope () (ExprU uv) a -> ExprU uv a

    -- Non-recursive
  Let :: SrcLoc -> String -> ExprU uv a -> Scope () (ExprU uv) a -> ExprU uv a

  Ann :: SrcLoc -> Type Void -> ExprU uv a -> ExprU uv a

  Comb :: SrcLoc -> Combinator -> ExprU uv a

infixl 0 :@
pattern (:@) :: ExprU uv a -> ExprU uv a -> ExprU uv a
pattern f :@ arg <- Apply _ f arg where
  f :@ arg = Apply NoSrcLoc f arg

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

-- instance (Show x) => Show1 (ExprU) where
--   liftShowsPrec = $(makeLiftShowsPrec ''ExprU)
deriveShow1 ''ExprU

deriving instance Functor (ExprU uv)
deriving instance Foldable (ExprU uv)
deriving instance Traversable (ExprU uv)

deriving instance (Show uv, Show a) => Show (ExprU uv a)

deriving instance Functor (WrappedExpr uv)
deriving instance Functor (ExprEq uv)
deriving instance Functor (Type)

deriving instance (Show a) => Show (Type a)

instance HasSrcLoc (ExprU uv a) where
  getSrcLoc (UVar srcLoc uv) = srcLoc
  getSrcLoc (Var srcLoc v) = srcLoc
  getSrcLoc (IntLit srcLoc i) = srcLoc
  getSrcLoc (BoolLit srcLoc b) = srcLoc
  getSrcLoc (Add srcLoc x y) = srcLoc
  getSrcLoc (Sub srcLoc x y) = srcLoc
  getSrcLoc (Mul srcLoc x y) = srcLoc
  getSrcLoc (Apply srcLoc x y) = srcLoc
  getSrcLoc (Lam srcLoc v body) = srcLoc
  getSrcLoc (Let srcLoc v e body) = srcLoc
  getSrcLoc (Ann srcLoc ty e) = srcLoc
  getSrcLoc (Comb srcLoc c) = srcLoc

  removeSrcLoc (UVar _ uv) = UVar NoSrcLoc uv
  removeSrcLoc (Var _ v) = Var NoSrcLoc v
  removeSrcLoc (IntLit _ i) = IntLit NoSrcLoc i
  removeSrcLoc (BoolLit _ b) = BoolLit NoSrcLoc b
  removeSrcLoc (Add _ x y) =
    Add NoSrcLoc (removeSrcLoc x) (removeSrcLoc y)
  removeSrcLoc (Sub _ x y) =
    Sub NoSrcLoc (removeSrcLoc x) (removeSrcLoc y)
  removeSrcLoc (Mul _ x y) =
    Mul NoSrcLoc (removeSrcLoc x) (removeSrcLoc y)
  removeSrcLoc (Apply _ x y) =
    Apply NoSrcLoc (removeSrcLoc x) (removeSrcLoc y)
  removeSrcLoc (Lam _ v body) =
    Lam NoSrcLoc v (hoistScope removeSrcLoc body)
  removeSrcLoc (Let _ v e body) =
    Let NoSrcLoc v (removeSrcLoc e) (hoistScope removeSrcLoc body)
  removeSrcLoc (Ann _ ty e) =
    Ann NoSrcLoc (removeSrcLoc ty) (removeSrcLoc e)
  removeSrcLoc (Comb _ c) = Comb NoSrcLoc c

instance Applicative (ExprU uv) where
  pure = Var NoSrcLoc
  (<*>) = ap

instance Monad (ExprU uv) where
  return = Var NoSrcLoc

  UVar _ x >>= _ = UVar NoSrcLoc x
  Var _ x >>= f = f x

  IntLit x i >>= _ = IntLit x i
  BoolLit x b >>= _ = BoolLit x b

  Add x a b >>= f = Add x (a >>= f) (b >>= f)
  Sub x a b >>= f = Sub x (a >>= f) (b >>= f)
  Mul x a b >>= f = Mul x (a >>= f) (b >>= f)

  Apply x a b >>= f = Apply x (a >>= f) (b >>= f)
  Lam x v e >>= f = Lam x v (e >>>= f)
  Let x v rhs body >>= f =
    Let x v (rhs >>= f) (body >>>= f)

  Ann x ty e >>= f = Ann x ty (e >>= f)
  Comb x c >>= _ = Comb x c

-- instance (Eq uv, Eq x) => Eq1 (ExprU uv) where
--   liftEq = $(makeLiftEq ''ExprU)
$(deriveEq1 ''ExprU)
-- deriveEq1 ''Type
-- instance (Ord uv, Ord x) => Ord1 (ExprU uv) where
--   liftCompare = $(makeLiftCompare ''ExprU)
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
wrappedExpr e = WrappedExpr e (==) compare show getSrcLoc removeSrcLoc


instance (Data uv, Data a, Ord uv, Ord a) => GraphNode (ExprU uv a) where
  -- nodeCost e = 1 + sum (map nodeCost (partsChildren e))
  nodeCost e = 1 + sum (map nodeCost (nodeChildren e))

instance Unify (ExprU) where
  isUVar (UVar _ x) = Just x
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
  toParts e@(UVar _ _) = Leaf e
  toParts e@(Var _ _) = Leaf e
  toParts e@(IntLit _ _) = Leaf e
  toParts e@(BoolLit _ _) = Leaf e

  toParts (Add x a b) = binaryParts a b (Add x)
  toParts (Sub x a b) = binaryParts a b (Sub x)
  toParts (Mul x a b) = binaryParts a b (Mul x)

  toParts (Apply x a b) = binaryParts a b (Apply x)

    -- TODO: Should we descend into these? If so, how?
  toParts e@(Lam {}) = Leaf e
  toParts e@(Let {}) = Leaf e

  toParts (Ann x ty e) = unaryParts e (Ann x ty)

-- instance Unify ExprU

-- | Top-level definition
data Def =
  Def
    { defType :: Type String
    , defBinding :: (String, [(SrcLoc, String)], Expr String)
    }

deriving instance Show Def

defName :: Def -> String
defName (Def _ (name, _, _)) = name

data TopLevel
  = TopLevelDef Def
  | Theorem (ExprEq Void String) -- Can also function as a rewrite

getDef :: TopLevel -> Maybe Def
getDef (TopLevelDef d) = Just d
getDef _ = Nothing

lam :: SrcLoc -> String -> Expr String -> Expr String
lam srcLoc v = Lam srcLoc v . abstract1 v

mkLams :: [(SrcLoc, String)] -> Expr String -> Expr String
mkLams [] body = body
mkLams ((srcLoc, arg):args) body = lam srcLoc arg (mkLams args body)

-- test1 :: Expr ()
-- test1 = Add (Mul (IntLit 5) (IntLit 1)) (Mul (IntLit 10) (IntLit 2))

-- test2 :: Expr ()
-- test2 = test1 `Mul` IntLit 1

-- reverseTest :: Def ()
-- reverseTest =
--   Def
--   { defType =
--       Refinement "rev" (ListType IntType .-> ListType IntType)
--         [ wrappedExpr (Var "rev" :@ Var "xs") :=: wrappedExpr (Var "rev" :@ (Var "rev" :@ Var "xs"))
--         , wrappedExpr (Var "append" :@ (Var "rev" :@ Var "ys") :@ (Var "rev" :@ Var "xs"))
--             :=:
--           wrappedExpr (Var "rev" :@ (Var "append" :@ Var "xs" :@ Var "ys"))
--         ] :: Type () String
--   , defBinding = ("reverse", ["xs"], undefined :: Expr () String)
--   }

defToExprAssoc :: Def -> (String, Expr String)
defToExprAssoc (Def ty (name, params, body)) = (name, mkLams params body)

-- rewrite1 :: Rewrite (ExprU ()) String ()
-- rewrite1 = toParts (Mul (UVar "?x") (IntLit 1)) :=> toParts (UVar "?x")

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
step env (Var _ v) =
  case lookup v env of
    Nothing -> error $ "No such binding " ++ show v
    Just e -> Just e

step _env (IntLit _ _) = Nothing
step _env (BoolLit _ _) = Nothing

step env (Add _ (IntLit _ x) (IntLit _ y)) = Just $ IntLit NoSrcLoc (x + y)
step env (Sub _ (IntLit _ x) (IntLit _ y)) = Just $ IntLit NoSrcLoc (x - y)
step env (Mul _ (IntLit _ x) (IntLit _ y)) = Just $ IntLit NoSrcLoc (x * y)

step env (Add _ x y) = stepApplyPair env (Add NoSrcLoc) x y
step env (Sub _ x y) = stepApplyPair env (Sub NoSrcLoc) x y
step env (Mul _ x y) = stepApplyPair env (Mul NoSrcLoc) x y

step env (Apply _ (Lam _ _ scoped) x) =
  Just $ instantiate1 x scoped

step env (Comb _ ConstF :@ x :@ y) = Just y
step env (Comb _ ComposeF :@ f :@ g :@ x) = Just (f :@ (g :@ x))
step env (Comb _ Nil) = Nothing
step env (Comb _ Head :@ (Comb _ Cons :@ x :@ xs)) = Just x
step env (Comb _ Tail :@ (Comb _ Cons :@ x :@ xs)) = Just xs
step env (Comb _ Foldr :@ f :@ z :@ (Comb _ Cons :@ x :@ xs)) =
  Just (f :@ x :@ (Comb NoSrcLoc Foldr :@ f :@ z :@ xs))

step env (Comb _ Le :@ IntLit _ x :@ IntLit _ y) = Just (BoolLit NoSrcLoc (x <= y))
step env (Comb _ Le :@ BoolLit _ x :@ BoolLit _ y) = Just (BoolLit NoSrcLoc (x <= y))
step env (Comb _ IntEq :@ IntLit _ x :@ IntLit _ y) = Just (BoolLit NoSrcLoc (x == y))

step env (Comb _ Not :@ BoolLit _ b) = Just (BoolLit NoSrcLoc (not b))
step env (Comb _ And :@ BoolLit _ x :@ BoolLit _ y) = Just (BoolLit NoSrcLoc (x && y))
step env (Comb _ Or :@ BoolLit _ x :@ BoolLit _ y) = Just (BoolLit NoSrcLoc (x || y))

step env (Comb _ Map :@ _ :@ Comb _ Nil) = Just $ Comb NoSrcLoc Nil
step env (Comb _ Map :@ f :@ (Comb _ Cons :@ x :@ xs)) = Just (Comb NoSrcLoc Cons :@ (f :@ x) :@ (Comb NoSrcLoc Map :@ f :@ xs))

step env (Comb _ Sum :@ Comb _ Nil) = Just $ IntLit NoSrcLoc 0
step env (Comb _ Sum :@ (Comb _ Cons :@ x :@ xs)) = Just (Add NoSrcLoc x (Comb NoSrcLoc Sum :@ xs))

-- step env (Comb Scanr :@ f :@ z :@ (Comb Cons :@ x :@ xs)) =
--   let v = fresh env
--   in
--   Let (
--   Comb Cons :@ 

  -- Non-strict evaluation order
step env (Apply _ f arg) = stepApplyPair env (Apply NoSrcLoc) f arg

step env (Lam {}) = Nothing

step env (Let _ _ rhs body) = Just $ instantiate1 rhs body

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

data Parens = WithParens | NoParens

withParens :: Parens -> String -> String
withParens WithParens s = "(" ++ s ++ ")"
withParens NoParens s = s

class Ppr a where
  pprP :: Parens -> a -> String

ppr :: Ppr a => a -> String
ppr = pprP NoParens

pprBinOp :: Ppr a => Parens -> String -> a -> a -> String
pprBinOp parens op x y =
  withParens parens $ pprP WithParens x ++ " " ++ op ++ " " ++ pprP WithParens y

instance Ppr a => Ppr (Var () a) where
  pprP _ (B ()) = "???"
  pprP _ (F v) = ppr v

instance (Ppr uv, Ppr a) => Ppr (ExprU uv a) where
  pprP parens (UVar _ uv) = ppr uv
  pprP parens (Var _ v) = ppr v
  pprP parens (IntLit _ i) = show i
  pprP parens (BoolLit _ b) = show b

  pprP parens (Add _ x y) = pprBinOp parens "+" x y
  pprP parens (Sub _ x y) = pprBinOp parens "-" x y
  pprP parens (Mul _ x y) = pprBinOp parens "*" x y

  pprP parens (Lam _ v body) =
    withParens parens $
      "\\ " ++ v ++ " -> " ++ ppr (unscope body)

  pprP parens (Let _ v bnd body) =
    withParens parens $
      "let " ++ v ++ " := " ++ ppr bnd
      ++ " in " ++ ppr (unscope body)

  pprP parens (Comb _ And :@ x :@ y) = pprBinOp parens "&&" x y
  pprP parens (Comb _ Or :@ x :@ y) = pprBinOp parens "||" x y
  pprP parens e@(Comb _ Cons :@ x :@ xs) =
    case getListExpr e of
      Nothing -> pprBinOp parens "::" x xs
      Just list -> pprList list

  pprP parens (Comb _ c) = pprP parens c

  pprP parens (Ann _ e ty) =
    withParens parens $
      ppr e ++ " : " ++ ppr ty

  pprP parens (f :@ x) =
    withParens parens $
      ppr f ++ " " ++ pprP WithParens x

instance (Ppr uv, Ppr a) => Ppr (ExprEq uv a) where
  pprP parens (wX :=: wY) =
    withParens parens $
      ppr (unwrapExpr wX) ++ " = " ++ ppr (unwrapExpr wY)

instance Ppr String where pprP _ = id

instance Ppr Void where
  pprP _ = absurd

instance Ppr SrcLoc where pprP _ = show -- TODO: Make this better

instance Ppr a => Ppr (Type a) where
  pprP parens (x :-> y) =
    withParens parens $
      pprP WithParens x ++ " -> " ++ ppr y

  pprP parens (TyVar _ x) = ppr x
  pprP _parens (BoolType _) = "Bool"
  pprP _parens (IntType _) = "Int"
  pprP parens (ListType _ a) =
    withParens parens $
      "List " ++ pprP WithParens a
  pprP _parens (UnitType _) = "unit"
  pprP parens (PairType _ a b) =
    withParens parens $
      "Pair " ++ pprP WithParens a ++ " " ++ pprP WithParens b

  pprP _parens (Refinement _ name ty eqs) =
    "{" ++ ppr name ++ " : " ++ ppr ty ++ " | " ++
      intercalate " & " (map ppr eqs) ++ "}"

instance Ppr Combinator where
  pprP _parens ConstF = "const"
  pprP _parens ComposeF = "compose"
  pprP _parens c = onHead toLower (show c)

instance Ppr Def where
  pprP _ (Def ty (name, params, body)) =
    unlines
      [ name ++ " : " ++ ppr ty ++ ";"
      , name ++ " " ++ intercalate " " (map snd params) ++ " := " ++ ppr body ++ ";"
      ]

onHead :: (a -> a) -> [a] -> [a]
onHead _ [] = []
onHead f (x:xs) = f x : xs

getListExpr :: ExprU uv a -> Maybe [ExprU uv a]
getListExpr (Comb _ Nil) = Just []
getListExpr (Comb _ Cons :@ x :@ xs) = fmap (x:) (getListExpr xs)
getListExpr _ = Nothing

pprList :: Ppr a => [a] -> String
pprList xs = 
    "[" ++ intercalate "," (map ppr xs) ++ "]"

