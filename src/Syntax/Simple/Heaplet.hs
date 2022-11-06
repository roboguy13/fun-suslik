{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}

module Syntax.Simple.Heaplet
  where

import           Syntax.Name
import           Syntax.Ppr

import           Text.Show.Deriving
import           Data.Functor.Classes
import           Data.Functor.Compose

import           Control.Monad
import           Data.List

import           GHC.Exts
import           GHC.Stack

import           Data.Void

type ConstrName = String

data ConcreteType = IntConcrete | BoolConcrete | LayoutConcrete LayoutName
  deriving (Show, Eq, Ord)

data LoweredType =
  MkLoweredType
  { loweredParams :: [String]
  , loweredType :: ConcreteType
  }
  deriving (Show, Eq)

data ExprX ty layoutNameTy a where
  Var :: ty -> a -> ExprX ty layoutNameTy a

  IntLit :: Int -> ExprX ty layoutNameTy a
  BoolLit :: Bool -> ExprX ty layoutNameTy a

  And :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  Or :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  Not :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a

  Add :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  Sub :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  Mul :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a

  Equal :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  Le :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  Lt :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a

  Apply ::
    String ->   -- | This becomes the appropriate predicate name in the elaborated version of ExprX
    ty ->       -- | Output layout
    [ExprX ty layoutNameTy a] ->
    ExprX ty layoutNameTy a

  ConstrApply :: ty -> ConstrName -> [ExprX ty layoutNameTy a] -> ExprX ty layoutNameTy a

  Lower :: layoutNameTy -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a

  Instantiate ::
    [layoutNameTy] ->
    layoutNameTy ->
    String ->
    [ExprX ty layoutNameTy a] ->
    ExprX ty layoutNameTy a

  --   -- | Represents @lower L_1 . f . lift L_2@
  -- LiftLowerFn ::
  --   layoutNameTy -> -- | L_1
  --   layoutNameTy -> -- | L_2
  --   ExprX ty layoutNameTy a -> -- | f
  --   ExprX ty layoutNameTy a

  -- ExprLayoutBranch :: [Heaplet a] -> Expr a

  -- ExprPointsTo :: Loc (Expr a) -> Expr a -> Expr a
  -- ExprHeapletApply :: String -> [Expr a] -> Expr a -> Expr a
  --
  -- ExprLayoutBranch :: Scope ParamIndex LayoutBranchE a -> Expr a

  -- LayoutCaseLambda :: Scope 
  deriving (Functor, Foldable, Traversable, Show)

-- TODO: Make this better
instance (Show a, Show layoutNameTy, Show ty) => Ppr (ExprX ty layoutNameTy a) where
    ppr = show

type ParsedExpr = ExprX () String
type ElaboratedExpr = ExprX LoweredType Void

type Parsed f = f () String
type Elaborated f = f LoweredType Void

type Expr = Elaborated ExprX

data Pattern a = MkPattern ConstrName [FsName] | PatternVar FsName
  deriving (Show)

getPatternVars :: Pattern a -> [FsName]
getPatternVars (MkPattern _ vs) = vs
getPatternVars (PatternVar v) = [v]

getBasicPatternVars :: [Pattern a] -> [FsName]
getBasicPatternVars = concatMap go
  where
    go (MkPattern _ _) = []
    go (PatternVar v) = [v]

isBasicPatternVar :: Pattern a -> Bool
isBasicPatternVar (PatternVar v) = True
isBasicPatternVar _ = False

data Def' cond body ty layoutNameTy =
  MkDef
  { defName :: String
  , defType :: Type
  , defBranches :: [DefBranch' cond body ty layoutNameTy]
  }
  deriving (Show)

-- fnArgTypes :: Type -> [Type]
-- fnArgTypes (FnType x y) =
--   x : fnArgTypes y
-- fnArgTypes _ = []
--
-- fnResultType :: Type -> Type
-- fnResultType (FnType _ t) = fnResultType t
-- fnResultType t = t

data DefBranch' cond body ty layoutNameTy=
  MkDefBranch
  { defBranchPattern :: [Pattern FsName]
  , defBranchGuardeds :: [GuardedExpr' cond body ty layoutNameTy]
  }
  deriving (Show)

getFirstBranch :: Def ty layoutNameTy -> DefBranch ty layoutNameTy
getFirstBranch MkDef{ defBranches = (b:_) } = b

data GuardedExpr' cond body ty layoutNameTy =
  MkGuardedExpr
  { guardedCond :: cond
  , guardedBody :: body
  }
  deriving (Show)

type Def ty layoutNameTy = Def' (ExprX ty layoutNameTy FsName) (ExprX ty layoutNameTy FsName) ty layoutNameTy
type DefBranch ty layoutNameTy = DefBranch' (ExprX ty layoutNameTy FsName) (ExprX ty layoutNameTy FsName) ty layoutNameTy
type GuardedExpr ty layoutNameTy = GuardedExpr' (ExprX ty layoutNameTy FsName) (ExprX ty layoutNameTy FsName) ty layoutNameTy

lookupDef :: [Def ty layoutNameTy] -> String -> Def ty layoutNameTy
lookupDef defs name =
  case find ((== name) . defName) defs of
    Nothing -> error $ "Cannot find function " ++ show name
    Just d -> d

data Type where
  IntType :: Type
  BoolType :: Type

  FnType :: Type -> Type -> Type

  -- AdtType :: Adt -> Type
  AdtType :: String -> Type
  -- LayoutType :: Layout -> Type
  LayoutType :: String -> Int -> Type
  deriving (Show)

getArgTypes :: Type -> [Type]
getArgTypes (FnType dom cod@(FnType {})) = dom : getArgTypes cod
getArgTypes (FnType dom cod) = [dom]
getArgTypes ty = error $ "getArgTypes: not a function type: " ++ show ty

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

findAdtBranch :: HasCallStack => Adt -> ConstrName -> AdtBranch
findAdtBranch adt cName =
  case find go (adtBranches adt) of
    Nothing -> error $ "findAdtBranch: Cannot find constructor " ++ cName ++ " in ADT " ++ (adtName adt)
    Just b -> b
  where
    go branch = adtBranchConstr branch == cName

lookupAdt :: HasCallStack => [Adt] -> String -> Adt
lookupAdt adts name =
  case find ((== name) . adtName) adts of
    Nothing -> error $ "lookupAdt: Cannot find ADT " ++ name
    Just a -> a

data Layout =
  MkLayout
  { layoutName :: String
  , layoutAdtName :: String
  , layoutSuSLikParams :: [SuSLikName]
  , layoutBranches :: [(Pattern FsName, Assertion FsName)]
  }
  deriving (Show)

lookupLayout :: HasCallStack => [Layout] -> String -> Layout
lookupLayout layoutDefs name =
  case find ((== name) . layoutName) layoutDefs of
    Nothing -> error $ "lookupLayout: Cannot find layout definition " ++ name
    Just def -> def

lookupLayoutBranch :: Layout -> ConstrName -> Assertion FsName
lookupLayoutBranch layout cName =
  case find (go . fst) $ layoutBranches layout of
    Nothing -> error $ "lookupLayoutBranch: Cannot find layout branch for " ++ show cName
    Just (_, b) -> b
  where
    go (MkPattern cName' _) = cName' == cName
    go (PatternVar {}) = True


-- instance Ppr a => Ppr (Expr a) where
--   ppr (Var v) = ppr v
--   ppr (IntLit i) = show i
--   ppr (BoolLit b) = show b
--
--   ppr (And x y) = pprBinOp "&&" x y
--   ppr (Or x y) = pprBinOp "||" x y
--   ppr (Not x) = "(not " ++ ppr x ++ ")"
--
--   ppr (Add x y) = pprBinOp "+" x y
--   ppr (Sub x y) = pprBinOp "-" x y
--   ppr (Mul x y) = pprBinOp "*" x y
--
--   ppr (Equal x y) = pprBinOp "==" x y
--   ppr (Le x y) = pprBinOp "<=" x y
--   ppr (Lt x y) = pprBinOp "<" x y
--
--   ppr (Apply f e) = "(" ++ f ++ " " ++ unwords (map ppr e) ++ ")"
--   ppr (ConstrApply cName args) =
--     "(" ++ cName ++ " " ++ unwords (map ppr args) ++ ")"
--
--   ppr (Lower str e) =
--     "(" ++ "lower" ++ unwords [str, ppr e] ++ ")"
--     -- "(" ++ "lower" ++ "[" ++ intercalate ", " (map ppr suslikArgs) ++ "] " ++ unwords [str, ppr e] ++ ")"
--   ppr (LiftLowerFn lName1 lName2 f) =
--     "(" ++ unwords ["lower", lName1, ".", ppr f, ".", "lift", lName2] ++ ")"
--
-- fsName, suslikName :: String -> Name
-- fsName = MkName
-- suslikName = MkName
--
data Mode = Input | Output
  deriving (Show, Eq, Ord)

data LayoutName =
  MkLayoutName
    (Maybe Mode) -- | This is Nothing if we are actually refering to a predicate generated for a function, rather than a layout
    String
  deriving (Show, Eq, Ord)

data Assertion a where
  Emp :: Assertion a
  PointsTo :: Mode -> Loc a -> ExprX () Void a -> Assertion a -> Assertion a
  HeapletApply :: LayoutName -> [a] -> [ExprX () Void a] -> Assertion a -> Assertion a
  deriving (Functor, Show, Foldable)

pattern PointsToI x y z = PointsTo Input x y z
pattern PointsToO x y z = PointsTo Output x y z

pattern HeapletApply' name xs ys rest = HeapletApply (MkLayoutName (Just Input) name) xs ys rest

genLayoutName :: LayoutName -> String
genLayoutName (MkLayoutName Nothing layoutName) = layoutName
genLayoutName (MkLayoutName (Just Input) layoutName) = "ro_" <> layoutName
genLayoutName (MkLayoutName (Just Output) layoutName) = "rw_" <> layoutName

setLayoutNameMode :: Maybe Mode -> LayoutName -> LayoutName
setLayoutNameMode mode (MkLayoutName _ name) = MkLayoutName mode name

setAssertionMode :: Mode -> Assertion a -> Assertion a
setAssertionMode mode = go
  where
    go Emp = Emp
    go (PointsTo _ x y rest) = PointsTo mode x y (go rest)
    go (HeapletApply name xs ys rest) = HeapletApply name xs ys (go rest)

instance (Show a, Ppr a) => Ppr (Assertion a) where
  ppr Emp = "emp"
  ppr (PointsTo mode x y rest) = unwords [ppr x, op, ppr y] ++ ", " ++ ppr rest
    where
      op =
        case mode of
          Input -> ":=>"
          Output -> ":->"
  ppr (HeapletApply lName suslikArgs fsArg rest) =
    unwords
      [genLayoutName lName ++ "[" ++ intercalate "," (map ppr suslikArgs) ++ "]"
      ,unwords (map ppr fsArg)
      ] ++ ", " ++ ppr rest

-- type Assertion' a = Assertion (ExprX () Void a)

--
-- -- exprMap :: (Expr a -> Expr a) -> (Assertion a -> Assertion a)
-- -- exprMap f = go
-- --   where
-- --     go Emp = Emp
-- --     go (PointsTo x e rest) = PointsTo x (f e) rest
-- --     go (HeapletApply lName suslikArgs e rest) = 
--
-- instance Semigroup (Assertion a) where
--   Emp <> b = b
--   PointsTo mode x y rest <> b = PointsTo mode x y (rest <> b)
--   HeapletApply lName suslikArgs e rest <> b = HeapletApply lName suslikArgs e (rest <> b)
--
-- instance Monoid (Assertion a) where
--   mempty = Emp
--
-- maybeToEndo :: (a -> Maybe a) -> (a -> a)
-- maybeToEndo f x =
--   case f x of
--     Nothing -> x
--     Just y -> y
--
-- substLayoutAssertion :: Int -> (Int -> LayoutName -> [Expr FsName] -> [Expr FsName] -> Maybe (Assertion' FsName)) -> Assertion' FsName -> Assertion' FsName
-- substLayoutAssertion _level _f Emp = Emp
-- substLayoutAssertion level f (PointsTo mode x y rest) = PointsTo mode x y (substLayoutAssertion level f rest)
-- substLayoutAssertion level f (HeapletApply lName suslikArgs e rest) =
--   case f level lName suslikArgs e of
--     Nothing -> HeapletApply lName suslikArgs e (substLayoutAssertion level f rest)
--     Just r -> r <> substLayoutAssertion (succ level) f rest
--
-- applyLayoutAssertion :: Eq a => [(a, a)] -> [(a, Expr a)] -> Assertion (Expr a) -> Assertion (Expr a)
-- applyLayoutAssertion suslikSubst fsSubst asn =
--   fmap go asn
--   where
--     go origV@(Var n) =
--       case lookup n suslikSubst of
--         Just s -> Var s
--         Nothing ->
--           case lookup n fsSubst of
--             Just e -> e
--             Nothing -> origV
--     go e = e
--
-- -- newtype LayoutBranch f a = MkLayoutBranch { getLayoutBranch :: [f a] }
-- --   deriving (Foldable, Traversable)
-- --               --ListT Expr
-- --
-- -- type LayoutBranchE = LayoutBranch Expr
-- -- type ScopeLayoutBranchE = Scope ParamIndex LayoutBranchE
-- --
-- -- instance IsList (LayoutBranch f a) where
-- --   type Item (LayoutBranch f a) = f a
-- --   fromList = MkLayoutBranch
-- --   toList = getLayoutBranch
-- --
-- -- instance Functor f => Functor (LayoutBranch f) where
-- --   fmap f (MkLayoutBranch xs) = MkLayoutBranch (map (fmap f) xs)
-- --
-- -- instance (Monad f, Traversable f) => Applicative (LayoutBranch f) where
-- --   pure x = MkLayoutBranch [pure x]
-- --   (<*>) = ap
-- --
-- -- instance (Monad f, Traversable f) => Monad (LayoutBranch f) where
-- --   return = pure
-- --   MkLayoutBranch xs >>= f = do
-- --     let zs = concatMap (map join) . fmap sequenceA . fmap (fmap getLayoutBranch) $ map (fmap f) xs
-- --     MkLayoutBranch zs
-- --
-- -- layoutBranchSingle :: Expr a -> LayoutBranchE a
-- -- layoutBranchSingle e = MkLayoutBranch [e]
--
-- instance Applicative Expr where
--   pure = Var
--   (<*>) = ap
--
-- instance Monad Expr where
--   return = pure
--
--   Var x >>= f = f x
--   IntLit i >>= _ = IntLit i
--   BoolLit b >>= _ = BoolLit b
--
--   And x y >>= f = And (x >>= f) (y >>= f)
--   Or x y >>= f = Or (x >>= f) (y >>= f)
--   Not x >>= f = Not (x >>= f)
--
--   Add x y >>= f = Add (x >>= f) (y >>= f)
--   Sub x y >>= f = Sub (x >>= f) (y >>= f)
--   Mul x y >>= f = Mul (x >>= f) (y >>= f)
--
--   Equal x y >>= f = Equal (x >>= f) (y >>= f)
--   Le x y >>= f = Le (x >>= f) (y >>= f)
--   Lt x y >>= f = Lt (x >>= f) (y >>= f)
--
--   Apply fName x >>= f = Apply fName (map (>>= f) x)
--
--   ConstrApply cName args >>= f = ConstrApply cName (map (>>= f) args)
--
--   Lower str x >>= f = Lower str (x >>= f)
--
--   LiftLowerFn l1 l2 x >>= f = LiftLowerFn l1 l2 (x >>= f)
--
--   -- ExprLayoutBranch xs >>= f = do
--   --   xs' <- traverse (traverse f) xs
--   --   ExprLayoutBranch xs'
--
--   -- ExprPointsTo x y >>= f = do
--   --   y' <- fmap f y
--   --   let x' = fmap (>>= f) x
--   --   ExprPointsTo x' y'
--   --
--   -- ExprHeapletApply x y z >>= f = do
--   --   y' <- traverse (fmap f) y
--   --   ExprHeapletApply x y' (z >>= f)
--
--
-- -- data Heaplet a where
-- --   PointsTo :: Loc a -> a -> Heaplet a
-- --   HeapletApply :: String -> [a] -> a -> Heaplet a
-- --   deriving (Show, Functor, Foldable, Traversable)
--
data Loc a = Here a | a :+ Int
  deriving (Show, Functor, Foldable, Traversable)

instance Ppr a => Ppr (Loc a) where
  ppr (Here x) = ppr x
  ppr (x :+ i) = "(" ++ ppr x ++ "+" ++ show i ++ ")"

instance Applicative Loc where
  pure = Here
  (<*>) = ap

instance Monad Loc where
  return = pure
  Here x >>= f = f x
  (x :+ i) >>= f = f x

-- {-
-- data BranchElement a where
--   MkBranchElement :: Heaplet a -> BranchElement a
--   BranchVar :: a -> BranchElement a -- | Represents an unknown (list of) heaplets using a SuSLikName
--   deriving (Show, Functor, Foldable, Traversable)
--
-- instance Applicative BranchElement where
--   pure = BranchVar
--   (<*>) = ap
--
-- instance Monad BranchElement where
--   return = pure
--   BranchVar x >>= f = f x
--   MkBranchElement (PointsTo (Here loc) y) >>= f = do
--     loc' <- f loc
--     y' <- f y
--     MkBranchElement (PointsTo (Here loc') y')
--   MkBranchElement (PointsTo (x :+ i) y) >>= f = do
--     x' <- f x
--     y' <- f y
--     MkBranchElement (PointsTo (x' :+ i) y')
--
--   MkBranchElement (HeapletApply layoutName xs ys) >>= f = do
--     xs' <- mapM f xs
--     ys' <- f ys
--     MkBranchElement $ HeapletApply layoutName xs' ys'
--
-- newtype LayoutBranch a = MkLayoutBranch { getLayoutBranch :: [BranchElement a] }
--   deriving (Show, Functor)
--
-- instance Applicative LayoutBranch where
--   pure x = MkLayoutBranch [pure x]
--   (<*>) = ap
--
-- instance Monad LayoutBranch where
--   return = pure
--   -- MkLayoutBranch xs0 >>= f = _ $ map (>>= (map _ . getLayoutBranch)) xs0
--   MkLayoutBranch xs0 >>= f =
--     let xs' = map (traverse f) xs0
--     in
--     MkLayoutBranch $ fmap join $ concatMap getLayoutBranch xs'
--     -- let xs' = map (_ f) xs0
--     -- in
--     -- undefined
--     -- MkLayoutBranch $ _ $ map (>>= concatMap (getLayoutBranch . _)) xs0
--
-- -- instance Applicative (LayoutBranch a) where
-- --   pure x = MkLayoutBranch [pure x]
-- --   (<*>) = ap
-- --
-- -- instance Monad (LayoutBranch a) where
-- --   return = pure
-- --   MkLayoutBranch xs0 >>= f = do
-- --     let xs0' = concatMap (getLayoutBranch . go) xs0
-- --
-- --     MkLayoutBranch xs0'
-- --     where
-- --       go (MkBranchElement (PointsTo (Here loc) y)) = do
-- --         loc' <- f loc
-- --
-- --         MkLayoutBranch $ [MkBranchElement (PointsTo (Here loc') y)]
-- --
-- --       go (MkBranchElement (HeapletApply layoutName xs ys)) = do
-- --         xs' <- mapM f xs
-- --         MkLayoutBranch $ [MkBranchElement (HeapletApply layoutName xs' ys)]
-- -}
--
-- $(deriveShow1 ''Loc)
-- -- $(deriveShow1 ''Heaplet)
-- -- $(deriveShow1 ''LayoutBranch)
-- $(deriveShow1 ''Expr)
-- -- $(deriveShow1 ''BranchElement)
--
-- deriving instance Show a => Show (Expr a)
-- -- deriving instance (Show (f a), Show a) => Show (LayoutBranch f a)
--
