{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Syntax.Simple.Heaplet
  where

import           Syntax.Name
import           Syntax.Ppr

import           Text.Show.Deriving
import           Data.Functor.Classes
import           Data.Functor.Compose

import           Control.Monad
import           Data.List
import           Data.Maybe

import           GHC.Exts hiding (toList)
import           GHC.Stack

import qualified Data.Map as Map

import           Data.Void

import           Data.Foldable

import Debug.Trace

type RecName = String

data SuSLikExpr a where
  VarS :: a -> SuSLikExpr a

  FnOutVar :: String -> SuSLikExpr a

  IntS :: Int -> SuSLikExpr a
  BoolS :: Bool -> SuSLikExpr a

  AndS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  OrS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  NotS :: SuSLikExpr a -> SuSLikExpr a

  LtS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  LeS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  EqualS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a

  AddS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  SubS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  MulS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a

  IteS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
  deriving (Show, Functor, Foldable)

instance Applicative SuSLikExpr where
  pure = return
  (<*>) = ap

instance Monad SuSLikExpr where
  return = VarS

  VarS x >>= f = f x
  FnOutVar x >>= _ = FnOutVar x
  IntS i >>= _ = IntS i
  BoolS b >>= _ = BoolS b
  AndS x y >>= f = AndS (x >>= f) (y >>= f)
  OrS x y >>= f = OrS (x >>= f) (y >>= f)
  NotS x >>= f = NotS (x >>= f)

  LtS x y >>= f = LtS (x >>= f) (y >>= f)
  LeS x y >>= f = LeS (x >>= f) (y >>= f)
  EqualS x y >>= f = EqualS (x >>= f) (y >>= f)

  AddS x y >>= f = AddS (x >>= f) (y >>= f)
  SubS x y >>= f = SubS (x >>= f) (y >>= f)
  MulS x y >>= f = MulS (x >>= f) (y >>= f)
  IteS x y z >>= f = IteS (x >>= f) (y >>= f) (z >>= f)


mkAndS :: SuSLikExpr a -> SuSLikExpr a -> SuSLikExpr a
mkAndS (BoolS True) y = y
mkAndS x (BoolS True) = x
mkAndS x y = AndS x y

ands :: [SuSLikExpr a] -> SuSLikExpr a
ands [] = BoolS True
ands (x:xs) = foldl1 mkAndS (x:xs)

instance Ppr a => Ppr (SuSLikExpr a) where
  ppr (VarS v) = ppr v
  ppr (FnOutVar v) = v
  ppr (IntS i) = show i
  ppr (BoolS True) = "true"
  ppr (BoolS False) = "false"

  ppr (AndS x y) = pprBinOp "&&" x y
  ppr (OrS x y) = pprBinOp "||" x y
  ppr (NotS x) = "(not " ++ ppr x ++ ")"

  ppr (AddS x y) = pprBinOp "+" x y
  ppr (SubS x y) = pprBinOp "-" x y
  ppr (MulS x y) = pprBinOp "*" x y

  ppr (EqualS x y) = pprBinOp "==" x y
  ppr (LeS x y) = pprBinOp "<=" x y
  ppr (LtS x y) = pprBinOp "<" x y

  ppr (IteS c t f) =
    "(" ++ ppr c ++ " ? " ++ ppr t ++ " : " ++ ppr f ++ ")"

type ConstrName = String

data ConcreteType' a = IntConcrete | BoolConcrete | LayoutConcrete a
  deriving (Show, Eq, Ord, Functor)

type ConcreteType = ConcreteType' LayoutName

type LoweredType = ConcreteType' ParametrizedLayoutName

-- data FsParam = IntParam String | BoolParam String | LayoutParam LayoutName [String]

withParams :: [String] -> ParamType -> ParamTypeP
withParams [v] (PtrParam _ ty) = PtrParam (Just (Here v)) ty
withParams [v] IntParam{} = IntParam (Just v)
withParams [v] BoolParam{} = BoolParam (Just v)
withParams params (LayoutParam name) = LayoutParam $ MkParametrizedLayoutName (map Here params) name

forgetParams :: LoweredType -> ConcreteType
forgetParams = fmap getParamedName

-- loweredParams :: LoweredType -> [String]
-- loweredParams IntConcrete = []
-- loweredParams BoolConcrete = []
-- loweredParams (LayoutConcrete (MkParametrizedLayoutName params _)) = params

loweredParams :: ParamTypeP -> [String]
loweredParams (PtrParam v _ty) = maybeToList (fmap ppr v)
loweredParams (IntParam v) = maybeToList v
loweredParams (BoolParam v) = maybeToList v
loweredParams (LayoutParam (MkParametrizedLayoutName params _)) = map getLocBase params -- TODO: Is this correct?

getParamedName :: ParametrizedLayoutName -> LayoutName
getParamedName (MkParametrizedLayoutName _ name) = name

getParamedNameParams :: ParametrizedLayoutName -> [Loc String]
getParamedNameParams (MkParametrizedLayoutName params _) = params

-- data LoweredType =
--   MkLoweredType
--   { loweredParams :: [String]
--   , loweredType :: ConcreteType
--   }
--   deriving (Show, Eq)

data ParamType' a
      = PtrParam (Maybe (Loc String)) BaseType
      | IntParam (Maybe String)
      | BoolParam (Maybe String)
      | LayoutParam a
      | FnParam -- | NOTE: This should not exist after defunctionalization
  deriving (Functor, Show, Eq, Ord)

type ParamType = ParamType' LayoutName

genParamTypeName :: ParamType -> String
genParamTypeName (PtrParam _ ty) = "Ptr " <> ppr ty
genParamTypeName IntParam{} = "Int"
genParamTypeName BoolParam{} = "Bool"
genParamTypeName (LayoutParam layoutName) = genLayoutName layoutName

-- paramTypeToConcrete :: ParamType' a -> ConcreteType' a
-- paramTypeToConcrete IntParam = IntConcrete
-- paramTypeToConcrete BoolParam = BoolConcrete
-- paramTypeToConcrete (LayoutParam x) = LayoutConcrete x

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
    [ty] ->     -- | Input layouts
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

  Deref :: ty -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  Addr :: ty -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a

  LetIn :: ty -> a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a 

  IfThenElse :: ty -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a

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

getType :: ExprX ty Void a -> Either BaseType ty
getType (Var ty _) = Right ty
getType (IntLit {}) = Left IntBase
getType (BoolLit {}) = Left BoolBase
getType (And {}) = Left BoolBase
getType (Or {}) = Left BoolBase
getType (Not {}) = Left BoolBase
getType (Add {}) = Left IntBase
getType (Sub {}) = Left IntBase
getType (Mul {}) = Left IntBase
getType (Equal {}) = Left BoolBase
getType (Le {}) = Left BoolBase
getType (Lt {}) = Left BoolBase
getType (Apply _ outTy _ _) = Right outTy
getType (ConstrApply ty _ _) = Right ty
getType (Lower x _) = absurd x
getType (Instantiate _ x _ _) = absurd x
getType (Deref ty _) = Right ty
getType (Addr ty _) = Right ty
getType (LetIn ty _ _ _) = Right ty
getType (IfThenElse ty _ _ _) = Right ty

-- getType' :: ElaboratedExpr a -> ParamTypeP
-- getType' e =
--   case getType e of
--     Left base -> _ $ baseToType base
--     Right ty -> ty

-- TODO: Make this better
instance (Show a, Show layoutNameTy, Show ty) => Ppr (ExprX ty layoutNameTy a) where
    ppr = show

type ParsedExpr = Parsed ExprX
type ElaboratedExpr = Elaborated ExprX

type Parsed f = f () ParamType
type Elaborated f = f ParamTypeP Void

type Expr = Elaborated ExprX

data Pattern' a = MkPattern a ConstrName [FsName] | PatternVar a FsName
  deriving (Show)

patternMapNames :: (FsName -> FsName) -> Pattern' a -> Pattern' a
patternMapNames f (MkPattern x cName args) = MkPattern x cName (map f args)
patternMapNames f (PatternVar x v) = PatternVar x (f v)

type Pattern = Pattern' ()

type PatternWithLayout = Pattern' ParametrizedLayoutName

patternSet :: b -> Pattern' a -> Pattern' b
patternSet x (MkPattern _ cName params) = MkPattern x cName params
patternSet x (PatternVar _ n) = PatternVar x n

getPatternVars :: Pattern' a -> [FsName]
getPatternVars (MkPattern _ _ vs) = vs
getPatternVars (PatternVar _ v) = [v]

getBasicPatternVars :: [Pattern' a] -> [FsName]
getBasicPatternVars = concatMap go
  where
    go (MkPattern _ _ _) = []
    go (PatternVar _ v) = [v]

isBasicPatternVar :: Pattern' a -> Bool
isBasicPatternVar (PatternVar _ v) = True
isBasicPatternVar _ = False

type ParamTypeP = ParamType' ParametrizedLayoutName

mkParamTypeP :: [String] -> ParamType -> ParamTypeP
mkParamTypeP [v] (PtrParam Nothing ty) = PtrParam (Just (Here v)) ty
mkParamTypeP [v] (IntParam Nothing) = IntParam (Just v)
mkParamTypeP [v] (BoolParam Nothing) = BoolParam (Just v) -- TODO: Should we handle the other cases differently?
mkParamTypeP params p = fmap (MkParametrizedLayoutName (map Here params)) p

updateParams :: [String] -> ParamType' a -> ParamType' a
updateParams [v] (PtrParam Nothing ty) = PtrParam (Just (Here v)) ty
updateParams [v] (IntParam Nothing) = IntParam (Just v)
updateParams [v] (BoolParam Nothing) = BoolParam (Just v)
updateParams _ p = p

overwriteParams :: [String] -> ParamType' a -> ParamType' a
overwriteParams [v] (IntParam {}) = IntParam (Just v)
overwriteParams [v] (BoolParam {}) = BoolParam (Just v)
overwriteParams _ p = p

data Def' defTy pat cond body ty layoutNameTy =
  MkDef
  { defName :: String
  , defType :: defTy
  , defBranches :: [DefBranch' pat cond body ty layoutNameTy]
  }
  deriving (Show)

-- TODO: Implement base type parameters:
-- type ElaboratedDef = Elaborated (DefT ([FsParam], FsParam) ParametrizedLayoutName)

type ElaboratedDef = Elaborated (DefT ([ParamTypeP], ParamTypeP) ParamTypeP)
type ParsedDef = Parsed (Def ())

fnArgTypes :: Type -> [Type]
fnArgTypes (FnType x y) =
  x : fnArgTypes y
fnArgTypes _ = []

fnResultType :: Type -> Type
fnResultType (FnType _ t) = fnResultType t
fnResultType t = t

data DefBranch' pat cond body ty layoutNameTy=
  MkDefBranch
  { defBranchPatterns :: [Pattern' pat]
  , defBranchGuardeds :: [GuardedExpr' cond body ty layoutNameTy]
  }
  deriving (Show)

type ElaboratedDefBranch = Elaborated (DefBranch ParamTypeP)
type ParsedDefBranch = Parsed (DefBranch ())


getFirstBranch :: Def pat ty layoutNameTy -> DefBranch pat ty layoutNameTy
getFirstBranch MkDef{ defBranches = (b:_) } = b

data GuardedExpr' cond body ty layoutNameTy =
  MkGuardedExpr
  { guardedCond :: cond
  , guardedBody :: body
  }
  deriving (Show)

type DefT defTy pat ty layoutNameTy = Def' defTy pat (ExprX ty layoutNameTy FsName) (ExprX ty layoutNameTy FsName) ty layoutNameTy

type Def pat ty layoutNameTy = DefT Type pat ty layoutNameTy

type DefBranch pat ty layoutNameTy = DefBranch' pat (ExprX ty layoutNameTy FsName) (ExprX ty layoutNameTy FsName) ty layoutNameTy
type GuardedExpr ty layoutNameTy = GuardedExpr' (ExprX ty layoutNameTy FsName) (ExprX ty layoutNameTy FsName) ty layoutNameTy

type GuardedExprWithAsn = Elaborated (GuardedExpr' (ElaboratedExpr FsName) (ExprWithAsn FsName))

type AsnGuarded = Elaborated (GuardedExpr' (ElaboratedExpr FsName) (Assertion FsName))

data ExprWithAsn a = MkExprWithAsn (Assertion a) (ElaboratedExpr a)
  deriving (Show)

type DefBranchWithAsn = Elaborated (DefBranch' ParamTypeP (ElaboratedExpr FsName) (ExprWithAsn FsName))
type AsnDefBranch = Elaborated (DefBranch' ParamTypeP (ElaboratedExpr FsName) (Assertion SuSLikName))

type DefWithAsn = Elaborated (Def' ([ParamTypeP], ParamTypeP) ParamTypeP (ElaboratedExpr FsName) (ExprWithAsn FsName))
type AsnDef = Elaborated (Def' ([ParamTypeP], ParamTypeP) ParamTypeP (ElaboratedExpr FsName) (Assertion FsName))

getDefRhs's :: Def' defTy pat cond body ty layoutNameTy -> [body]
getDefRhs's = concatMap getDefBranchRhs's . defBranches

getDefBranchRhs's :: DefBranch' pat cond body ty layoutNameTy -> [body]
getDefBranchRhs's = map getGuardedRhs . defBranchGuardeds

getGuardedRhs :: GuardedExpr' cond body ty layoutNameTy -> body
getGuardedRhs (MkGuardedExpr _ x) = x

lookupDef :: HasCallStack => [Def' defTy pat cond body ty layoutNameTy] -> String -> Def' defTy pat cond body ty layoutNameTy
lookupDef defs name =
  case find ((== name) . defName) defs of
    Nothing -> error $ "Cannot find function " ++ show name
    Just d -> d

data BaseType where
  IntBase :: BaseType
  BoolBase :: BaseType
  deriving (Show, Eq, Ord)

instance Ppr BaseType where
  ppr IntBase = "Int"
  ppr BoolBase = "Bool"

data Type where
  IntType :: Type
  BoolType :: Type

  PtrType :: BaseType -> Type

  FnType :: Type -> Type -> Type

  -- AdtType :: Adt -> Type
  AdtType :: String -> Type
  -- LayoutType :: Layout -> Type
  LayoutType :: String -> Int -> Type
  deriving (Show)

baseToType :: BaseType -> Type
baseToType IntBase = IntType
baseToType BoolBase = BoolType

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
  , layoutBranches :: [(Pattern, Assertion FsName)]
  }
  deriving (Show)

toSuSLikExpr :: RecName -> Expr FsName -> SuSLikExpr SuSLikName
toSuSLikExpr _ (Var _ v) = VarS v
toSuSLikExpr _ (IntLit i) = IntS i
toSuSLikExpr _ (BoolLit b) = BoolS b
toSuSLikExpr recName (And x y) = AndS (toSuSLikExpr recName x) (toSuSLikExpr recName y)
toSuSLikExpr recName (Or x y) = OrS (toSuSLikExpr recName x) (toSuSLikExpr recName y)
toSuSLikExpr recName (Not x) =
  NotS (toSuSLikExpr recName x)

toSuSLikExpr recName (Add x y) = AddS (toSuSLikExpr recName x) (toSuSLikExpr recName y)
toSuSLikExpr recName (Sub x y) = SubS (toSuSLikExpr recName x) (toSuSLikExpr recName y)
toSuSLikExpr recName (Mul x y) = MulS (toSuSLikExpr recName x) (toSuSLikExpr recName y)

toSuSLikExpr recName (Equal x y) = EqualS (toSuSLikExpr recName x) (toSuSLikExpr recName y)
toSuSLikExpr recName (Le x y) = LeS (toSuSLikExpr recName x) (toSuSLikExpr recName y)
toSuSLikExpr recName (Lt x y) = LtS (toSuSLikExpr recName x) (toSuSLikExpr recName y)

toSuSLikExpr recName e0@(Apply f outTy inTys args) =
  head $ map (mkVar (f == recName)) (loweredParams outTy)
  -- head $ map FnOutVar (loweredParams outTy)
  -- head $ map VarS (loweredParams outTy)

toSuSLikExpr recName e0@(ConstrApply ty cName args) = 
  head $ map VarS (loweredParams ty)

toSuSLikExpr recName (Deref ty e) =
  head $ map VarS (loweredParams ty)

toSuSLikExpr recName (Addr ty e) =
  head $ map VarS (loweredParams ty)

toSuSLikExpr recName (LetIn ty v rhs body) =
  toSuSLikExpr recName body

toSuSLikExpr recName (IfThenElse _ cond t f) =
  IteS (toSuSLikExpr recName cond) (toSuSLikExpr recName t) (toSuSLikExpr recName f)

toSuSLikExpr' :: Expr FsName -> SuSLikExpr SuSLikName
toSuSLikExpr' = toSuSLikExpr ""

mkVar :: Bool -> FsName -> SuSLikExpr FsName
mkVar isRecCall n
  | isRecCall = VarS n
  | otherwise = FnOutVar n

naiveSubst :: (Eq a, Functor f) => [(a, a)] -> f a -> f a
naiveSubst [] fa = fa
naiveSubst ((old, new):rest) fa = naiveSubst rest (fmap go fa)
  where
    go y
      | y == old = new
      | otherwise = y

naiveSubstAsn1 :: (FsName, SuSLikExpr FsName) -> Assertion FsName -> Assertion FsName
naiveSubstAsn1 subst@(old, new) fa =
    case fa of
      Emp -> Emp

      PointsTo mode x y@(VarS v) rest ->
        if v == old
          then PointsTo mode x new (naiveSubstAsn1 subst rest)
          else PointsTo mode x y (naiveSubstAsn1 subst rest)
      PointsTo mode x y rest -> PointsTo mode x y (naiveSubstAsn1 subst rest)

      HeapletApply fName suslikParams fsArgs rest ->
        HeapletApply fName (map (>>= go) suslikParams) fsArgs rest

      Block v sz rest -> 
        Block v sz (naiveSubstAsn1 subst rest)

      TempLoc v rest ->
        TempLoc v (naiveSubstAsn1 subst rest)

      IsNull _ -> fa
      Copy _ _ _ -> fa
      AssertEqual lhs rhs@(VarS v) rest
        | v == old -> AssertEqual lhs new (naiveSubstAsn1 subst rest)
        | otherwise -> AssertEqual lhs rhs (naiveSubstAsn1 subst rest)
      AssertEqual lhs rhs rest ->
        AssertEqual lhs rhs (naiveSubstAsn1 subst rest)
  where
    go x
      | x == old = new
      | otherwise = VarS x

naiveSubstAsn :: [(FsName, SuSLikExpr FsName)] -> Assertion FsName -> Assertion FsName
naiveSubstAsn [] fa = fa
naiveSubstAsn (subst:rest) fa = naiveSubstAsn rest (naiveSubstAsn1 subst fa)

mangleLayout :: Layout -> Layout
mangleLayout layout =
  let r = layout
            { layoutSuSLikParams = map mangle (layoutSuSLikParams layout)
            , layoutBranches = map go (layoutBranches layout)
            }
  in
  r
  where
    go (pat, asn) = (patternMapNames mangle pat, fmap mangle asn)

layoutMatch :: Layout -> ConstrName -> [SuSLikName] -> Assertion SuSLikName
layoutMatch layout0 cName args =
  let layout = mangleLayout layout0
      (MkPattern _ _ params, asn) = lookupLayoutBranch layout cName
  in
  naiveSubst (zip params args) asn

-- layoutMatchPat :: Show a => Layout -> Pattern' a -> Assertion SuSLikName
-- layoutMatchPat layout e@(PatternVar {}) = error $ "layoutMatch: Pattern variable: " ++ show e
-- layoutMatchPat layout (MkPattern _ cName args) = layoutMatch layout cName args

layoutMatchPat :: Show a => Layout -> Pattern' a -> Assertion SuSLikName
layoutMatchPat layout e@(PatternVar {}) = error $ "layoutMatch: Pattern variable: " ++ show e
layoutMatchPat layout (MkPattern _ cName args) = 
  let (MkPattern _ _ params, asn) = lookupLayoutBranch layout cName
  in
  naiveSubst (zip params args) asn

applyLayoutPat :: Show a => Layout -> [String] -> Pattern' a -> Assertion SuSLikName
applyLayoutPat layout0 suslikParams pat =
  let layout = mangleLayout layout0
  in
  fmap unmangle $
  substSuSLikParams
    (layoutSuSLikParams layout) suslikParams
    (layoutMatchPat layout pat)

applyLayout :: Layout -> [SuSLikName] -> ConstrName -> [SuSLikName] -> Assertion SuSLikName
applyLayout layout0 suslikParams cName args =
  let layout = mangleLayout layout0
  in
  fmap unmangle $
  substSuSLikParams
    (layoutSuSLikParams layout) suslikParams
    (layoutMatch layout cName args)

applyLayoutExpr :: Layout -> [SuSLikName] -> ConstrName -> [SuSLikExpr FsName] -> Assertion SuSLikName
applyLayoutExpr layout0 suslikParams cName args =
  let layout = mangleLayout layout0
      (MkPattern _ _ params, asn0) = lookupLayoutBranch layout cName
      mangledAsn =
        substSuSLikParams (layoutSuSLikParams layout) suslikParams asn0
      subst = zip params args
      r = fmap unmangle $ naiveSubstAsn subst mangledAsn
  in
  -- trace ("subst = " ++ show subst) $
  -- trace ("mangledAsn = " ++ show mangledAsn) $
  -- trace ("r = " ++ show r) $
  r

-- | NOTE: Also inserts [..., ...] block sizes
substSuSLikParams ::
  [SuSLikName] -> [SuSLikName] -> Assertion SuSLikName -> Assertion SuSLikName
substSuSLikParams olds news asn =
  let asn' = naiveSubst (zip olds news) asn 
      blocks = getBlocks asn'
  in
  asn' <> blocks

lookupLayout :: HasCallStack => [Layout] -> String -> Layout
lookupLayout layoutDefs name =
  case find ((== name) . layoutName) layoutDefs of
    Nothing -> error $ "lookupLayout: Cannot find layout definition " ++ name
    Just def -> def

lookupLayoutBranch :: Layout -> ConstrName -> (Pattern, Assertion FsName)
lookupLayoutBranch layout cName =
  case find (go . fst) $ layoutBranches layout of
    Nothing -> error $ "lookupLayoutBranch: Cannot find layout branch for " ++ show cName
    Just b -> b
  where
    go (MkPattern _ cName' _) = cName' == cName
    go (PatternVar {}) = True

getBlocks :: Assertion FsName -> Assertion FsName
getBlocks =
  foldMap (\(n, i) -> Block n i Emp) . getBlockSizes

pointsLocs :: Assertion a -> [Loc a]
pointsLocs Emp = []
pointsLocs (PointsTo _mode x _ rest) = x : pointsLocs rest
pointsLocs (HeapletApply _ _ _ rest) = pointsLocs rest
pointsLocs (Block _ _ rest) = pointsLocs rest
pointsLocs (TempLoc _ rest) = pointsLocs rest
pointsLocs (IsNull _) = []
pointsLocs (Copy _ _ _) = []
pointsLocs (AssertEqual _ _ rest) = pointsLocs rest

getBlockSizes :: Assertion FsName -> [(FsName, Int)]
getBlockSizes asn =
  Map.toList $ foldr (uncurry (Map.insertWith max)) Map.empty locPairs
  where
    locPairs = mapMaybe locToPair (pointsLocs asn)

    locToPair (Here {}) = Nothing
    locToPair (x :+ i) = Just (x, i+1)


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

data ParametrizedLayoutName =
  MkParametrizedLayoutName
    [Loc String]
    LayoutName
  deriving (Show, Eq, Ord)

overParams :: (Loc String -> Loc String) -> ParametrizedLayoutName -> ParametrizedLayoutName
overParams f (MkParametrizedLayoutName xs n) = MkParametrizedLayoutName (map f xs) n

pattern MkLowered params name = LayoutConcrete (MkParametrizedLayoutName params name)

layoutNameHasMode :: LayoutName -> Bool
layoutNameHasMode (MkLayoutName Nothing _) = False
layoutNameHasMode (MkLayoutName Just{} _) = True


baseLayoutName :: LayoutName -> String
baseLayoutName (MkLayoutName _ name) = name

exprForget :: Show a => Expr a -> ExprX () Void a
exprForget (Var _ v) = Var () v
exprForget (IntLit i) = IntLit i
exprForget (BoolLit b) = BoolLit b
exprForget (And x y) = And (exprForget x) (exprForget y)
exprForget (Or x y) = Or (exprForget x) (exprForget y)
exprForget (Not x) = Not (exprForget x)
exprForget (Add x y) = Add (exprForget x) (exprForget y)
exprForget (Sub x y) = Sub (exprForget x) (exprForget y)
exprForget (Mul x y) = Mul (exprForget x) (exprForget y)
exprForget (Equal x y) = Equal (exprForget x) (exprForget y)
exprForget (Le x y) = Le (exprForget x) (exprForget y)
exprForget (Lt x y) = Lt (exprForget x) (exprForget y)
exprForget (Apply f _ suslikArgs args) = Apply f () (replicate (length suslikArgs) ()) (map exprForget args)
exprForget (ConstrApply _ cName args) = ConstrApply () cName (map exprForget args)
exprForget e = error $ "exprForget: " ++ show e

  -- IntLit
  -- BoolLit

  -- And :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  -- Or :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  -- Not :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  --
  -- Add :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  -- Sub :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  -- Mul :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  --
  -- Equal :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  -- Le :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  -- Lt :: ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a -> ExprX ty layoutNameTy a
  --
  -- Apply ::
  --   String ->   -- | This becomes the appropriate predicate name in the elaborated version of ExprX
  --   ty ->       -- | Output layout
  --   [ty] ->     -- | Input layouts
  --   [ExprX ty layoutNameTy a] ->
  --   ExprX ty layoutNameTy a
  --
  -- ConstrApply :: ty -> ConstrName -> [ExprX ty layoutNameTy a] -> ExprX ty layoutNameTy a
  --
data Assertion a where
  Emp :: Assertion a
  PointsTo :: Mode -> Loc a -> SuSLikExpr a -> Assertion a -> Assertion a
  HeapletApply :: LayoutName -> [SuSLikExpr a] -> [ExprX () Void a] -> Assertion a -> Assertion a

  TempLoc :: SuSLikName -> Assertion a -> Assertion a
  Block :: SuSLikName -> Int -> Assertion a -> Assertion a

  IsNull :: a -> Assertion a
  Copy :: String -> a -> a -> Assertion a

  AssertEqual :: a -> SuSLikExpr a -> Assertion a -> Assertion a
  deriving (Functor, Show, Foldable)

isEmp :: Assertion a -> Bool
isEmp Emp = True
isEmp _ = False

removeHeapletApplies :: LayoutName -> Assertion FsName -> Assertion FsName
removeHeapletApplies _ Emp = Emp
removeHeapletApplies recName (PointsTo mode x y rest) =
  PointsTo mode x y (removeHeapletApplies recName rest)
removeHeapletApplies recName (HeapletApply lName x y rest)
  | baseLayoutName lName == baseLayoutName recName = removeHeapletApplies recName rest
  | otherwise = HeapletApply lName x y (removeHeapletApplies recName rest)
removeHeapletApplies recName (Block v sz rest) = Block v sz (removeHeapletApplies recName rest)
removeHeapletApplies recName (TempLoc v rest) = TempLoc v (removeHeapletApplies recName rest)
removeHeapletApplies recName asn@(IsNull _) = asn
removeHeapletApplies recName asn@(Copy _ _ _) = asn
removeHeapletApplies recName (AssertEqual _ _ rest) = removeHeapletApplies recName rest

instance Semigroup (Assertion a) where
  Emp <> x = x
  x <> Emp = x

  IsNull _ <> _ = error "Cannot combine IsNull with another Assertion"
  _ <> IsNull _ = error "Cannot combine IsNull with another Assertion"

  Copy _ _ _ <> _ = error "Cannot combine Copy with another Assertion"
  _ <> Copy _ _ _ = error "Cannot combine Copy with another Assertion"


  PointsTo mode loc e rest <> y =
    PointsTo mode loc e (rest <> y)

  HeapletApply lName params args rest <> y =
    HeapletApply lName params args (rest <> y)

  Block v i rest <> y = Block v i (rest <> y)

  TempLoc v rest <> y = TempLoc v (rest <> y)

  AssertEqual x y rest <> z = AssertEqual x y (rest <> z)

instance Monoid (Assertion a) where
  mempty = Emp

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
    go (Block v sz rest) =
      Block v sz (go rest)

    go (TempLoc v rest) =
      TempLoc v (go rest)

    go asn@(IsNull _) = asn
    go asn@(Copy _ _ _) = asn
    go (AssertEqual x y rest) = AssertEqual x y (go rest)

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
  ppr (Block v sz rest) =
    "[" ++ v ++ ", " ++ show sz ++ "]" ++ ", " ++ ppr rest
  ppr (TempLoc v rest) =
    "temploc " ++ v ++ ", " ++ ppr rest

  ppr (IsNull v) = ppr v ++ " == null ; emp"
  ppr (Copy lName src dest) = "func " ++ lName ++ "__copy(" ++ ppr src ++ ", " ++ ppr dest ++ ")"
  ppr (AssertEqual x y rest0) = "(" <> ppr x <> " == " <> ppr y <> ")"

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
  deriving (Show, Functor, Foldable, Traversable, Eq, Ord)

getLocBase :: Loc a -> a
getLocBase (Here x) = x
getLocBase (x :+ _) = x

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
