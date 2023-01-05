--
-- Basic type checking and elaboration
--
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Syntax.Simple.TypeCheck
  where

import           Syntax.Simple.Heaplet
import           Syntax.FreshGen
import           Syntax.Name

import           Data.List
import           Data.Maybe
import           Data.Void

import           Control.Monad.Reader
import           Control.Monad.State

import           Control.Arrow

import           GHC.Stack

import Debug.Trace

data TcGlobals = MkTcGlobals String [Layout] [Adt] [Parsed (Def ())]

newtype TypeCheck a = MkTypeCheck (ReaderT TcGlobals (Either String) a)
  deriving (Functor, Applicative, Monad, MonadReader TcGlobals)

instance MonadFail TypeCheck where
  fail = error

runTypeCheck :: String -> [Layout] -> [Adt] -> [Parsed (Def ())] -> TypeCheck a -> a
runTypeCheck fnName layouts adts defs (MkTypeCheck tc) =
  let globals = MkTcGlobals fnName layouts adts defs
  in
  case runReaderT tc globals of
    Left err -> error err
    Right x -> x

type TcEnv = [(String, ParamType)]

lookupLayoutM :: String -> TypeCheck Layout
lookupLayoutM name = do
  MkTcGlobals _ layouts _ _ <- ask
  pure $ lookupLayout layouts name

getLayouts :: TypeCheck [Layout]
getLayouts = do
  MkTcGlobals _ layouts _ _ <- ask
  pure layouts

type ParamTypeL = ParamType' Layout

lookupParamType :: ParamType -> TypeCheck ParamTypeL
lookupParamType (PtrParam v ty) = pure $ PtrParam v ty
lookupParamType (IntParam v) = pure $ IntParam v
lookupParamType (BoolParam v) = pure $ BoolParam v
lookupParamType (LayoutParam layoutName) = LayoutParam <$> lookupLayoutM (baseLayoutName layoutName)

lookupAdtM :: String -> TypeCheck Adt
lookupAdtM name = do
  MkTcGlobals _ _ adts _ <- ask
  pure $ lookupAdt adts name

lookupDefM :: String -> TypeCheck (Parsed (Def ()))
lookupDefM name = do
  MkTcGlobals _ _ _ defs <- ask
  pure $ lookupDef defs name

getCurrFnName :: TypeCheck String
getCurrFnName = do
  MkTcGlobals f _ _ _ <- ask
  pure f

typeError :: HasCallStack => String -> TypeCheck a
typeError err = error err --MkTypeCheck . lift . lift . lift $ Left err

requireType :: (Eq a, Show a) => a -> a -> TypeCheck ()
requireType expected found =
  if expected == found
    then pure ()
    else typeError $ "Expected type " ++ show expected ++ ", found " ++ show found

-- | Get the predicate name for a function with the given layouts
getPredName :: String -> [String] -> String -> String
getPredName fnName argLayouts resultLayout =
  fnName <> "__" <> intercalate "__" (map (replace ' ' '_') (resultLayout : argLayouts))

replace :: Eq a => a -> a -> [a] -> [a]
replace _ _ [] = []
replace x x' (y:ys)
  | y == x = x' : replace x x' ys
  | otherwise = y : replace x x' ys

-- Also updates the Def name
instAndElaborate :: String -> [ParamType] -> ParamType -> ParsedDef -> TypeCheck ElaboratedDef
instAndElaborate fnName argParamTypes outParamType def = do
  let oldName = defName def
  elaborated <- elaborateDef argParamTypes outParamType
                  $ instDefCalls argParamTypes outParamType def
  pure $ elaborated
    { defName = oldName --(getPredName oldName (map genParamTypeName argParamTypes) (genParamTypeName outParamType))
    }

instDefCalls :: [ParamType] -> ParamType -> ParsedDef -> ParsedDef
instDefCalls argParamTypes outParamType def =
  def
    { defBranches = map goBranch (defBranches def)
    }
  where
    goBranch branch =
      branch
        { defBranchGuardeds = map goGuarded (defBranchGuardeds branch)
        }
    goGuarded (MkGuardedExpr x y) =
      MkGuardedExpr (go x) (go y)

    go = instCall (defName def) argParamTypes outParamType

-- | Any call to the given function gets surrounded by an instantiation with
-- the given layouts. This is useful for recursive calls.
-- If it encounters an application of the function that is instantiated
-- to different layouts, it leaves that instantiation unchanged.
instCall :: String -> [ParamType] -> ParamType -> Parsed ExprX String -> Parsed ExprX String
instCall fnName argParamTypes outParamType = go
  where
    instantiate = Instantiate argParamTypes outParamType fnName
    go e@(Var {}) = e
    go e@(IntLit {}) = e
    go e@(BoolLit {}) = e
    go (And x y) = And (go x) (go y)
    go (Or x y) = Or (go x) (go y)
    go (Not x) = Not (go x)
    go (Add x y) = Add (go x) (go y)
    go (Sub x y) = Sub (go x) (go y)
    go (Mul x y) = Mul (go x) (go y)
    go (Equal x y) = Equal (go x) (go y)
    go (Le x y) = Le (go x) (go y)
    go (Lt x y) = Lt (go x) (go y)
    go (Apply f ty argTys args) -- TODO: Put in a sanity check for the layouts
      | f == fnName = instantiate (map go args)
      | otherwise = Apply f ty argTys (map go args)
    go (ConstrApply ty cName args) = ConstrApply ty cName (map go args)
    go (Lower layout arg) = Lower layout (go arg)
    go (Instantiate xs ys f args) = Instantiate xs ys f (map go args)
    go (Deref ty e) = Deref ty (go e)
    go (Addr ty e) = Addr ty (go e)
    go (LetIn ty v rhs body) =
      LetIn ty v (go rhs) (go body)
    go (IfThenElse ty c t f) =
      IfThenElse ty (go c) (go t) (go f)

paramTypeToLayout :: ParamTypeL -> Maybe Layout
paramTypeToLayout (LayoutParam layout) = Just layout
paramTypeToLayout _ = Nothing

-- paramTypeToConcrete :: ParamTypeL

isPatternVar :: Pattern' a -> Bool
isPatternVar PatternVar{} = True
isPatternVar _ = False

elaborateDef :: [ParamType] -> ParamType -> ParsedDef -> TypeCheck ElaboratedDef
elaborateDef inParamTypes outParamType def = do
  foundArgTypes <- mapM lookupParamType inParamTypes
  argAdts <- mapM (traverse (lookupAdtM . layoutAdtName)) (map paramTypeToLayout foundArgTypes)
  foundOutType <- lookupParamType outParamType

  let goBranch :: ParsedDefBranch -> TypeCheck ElaboratedDefBranch
      goBranch defBranch = do
          let gamma = map snd $ concat $ zipWith3 inferLayoutPatVars foundArgTypes argAdts $ defBranchPatterns defBranch

          let goGuarded (MkGuardedExpr x y) = do
                MkGuardedExpr <$> goExpr x <*> goExpr y

              goExpr e = do
                (_ty, e') <- inferWith gamma outParamType e
                pure e'

          guardeds <- mapM (\x -> goGuarded x) (defBranchGuardeds defBranch)
            :: TypeCheck [GuardedExpr' (ElaboratedExpr String) (ElaboratedExpr String) ParamType Void]

          pure $ defBranch
            { defBranchGuardeds = guardeds
            }

  defBranches' <- mapM goBranch (defBranches def)

  pure $ def
    { defBranches = defBranches'
    , defType = (inParamTypes, outParamType)
    }

inferLayoutPatVars :: ParamTypeL -> Maybe Adt -> Pattern -> [(Pattern, (FsName, ParamType))]
inferLayoutPatVars (PtrParam p ty) _ pat@(PatternVar _ v) =
  [(pat, (v, PtrParam p ty))]
inferLayoutPatVars (BoolParam p) _ pat@(PatternVar _ v) = [(pat, (v, BoolParam p))]
inferLayoutPatVars (IntParam p) _ pat@(PatternVar _ v) = [(pat, (v, IntParam p))]
inferLayoutPatVars (BoolParam p) _ pat = error $ "Attempt to pattern match on Bool: " ++ show pat
inferLayoutPatVars (IntParam p) _ pat = error $ "Attempt to pattern match on Int: " ++ show pat
inferLayoutPatVars (LayoutParam layout) (Just adt) pat@(PatternVar _ v) =
    let suslikNames = map (patternVarSuSLikName v) (layoutSuSLikParams layout)
    in
    [(pat, (v, LayoutParam (MkLayoutName (Just Input) (layoutName layout))))]
inferLayoutPatVars (LayoutParam layout) (Just adt) pat@(MkPattern _ cName params) =
    let adtFields = adtBranchFields $ findAdtBranch adt cName
    in
    map (pat,) $ zipWith go params adtFields
  where
    appliedLayout = applyLayoutPat layout [] pat

    patVarMappings0 = layoutPatternNames layout pat

    go v IntType = (v, IntParam $ Just v) -- TODO: Or should these be Nothing?
    go v BoolType = (v, BoolParam $ Just v)
    go v _ =
      (v, LayoutParam $ findLayoutApp v appliedLayout)
      -- (v, withParams suslikNames $ LayoutParam $ findLayoutApp v appliedLayout)
inferLayoutPatVars (LayoutParam layout) Nothing _ = error $ "inferLayoutPatVars: Could not find ADT associated to layout " ++ show layout

findLayoutApp :: FsName -> Assertion FsName -> LayoutName
findLayoutApp v asn0 = go asn0
  where
    go :: Assertion FsName -> LayoutName
    go Emp = error $ "findLayoutApp: Cannot find " ++ show v ++ "\nasn0 = " ++ show asn0
    go (PointsTo _ _ _ rest) = go rest
    go (HeapletApply lName params [Var _ v'] rest)
      | v' == v = lName
      | otherwise = go rest
    go (HeapletApply lName params _ rest) = go rest
    go (TempLoc _ rest) = go rest
    go (Block _ _ rest) = go rest
    go (IsNull _) = error $ "findLayoutApp: Cannot find " ++ show v ++ "\nasn0 = " ++ show asn0
    go (Copy _ _ _) = error $ "findLayoutApp: Cannot find " ++ show v ++ "\nasn0 = " ++ show asn0
    go (AssertEqual _ _ rest) = go rest

lowerWith :: ParamType -> Parsed ExprX String -> Parsed ExprX String
lowerWith ty@(LayoutParam{}) e@(ConstrApply {}) =
  Lower ty e
lowerWith ty e@(ConstrApply {}) = error $ "Constructor application of non-layout type:\nType = " ++ show ty ++ "\nExpr = " ++ show e ++ "\n"
lowerWith ty (LetIn ty' v rhs body) =
  LetIn ty' v rhs (lowerWith ty body)
lowerWith ty (IfThenElse ty' c t f) =
  IfThenElse ty' c (lowerWith ty t) (lowerWith ty f)
lowerWith _ e = e

inferWith :: TcEnv -> ParamType -> Parsed ExprX String -> TypeCheck (ParamType, ElaboratedExpr String)
inferWith gamma ty e = inferExpr gamma (lowerWith ty e)

requireIntParam :: Show a => ParamType' a -> TypeCheck ()
requireIntParam IntParam{} = pure ()
requireIntParam p = typeError $ "Expecting Int, found " ++ show p

requireBoolParam :: Show a => ParamType' a -> TypeCheck ()
requireBoolParam BoolParam{} = pure ()
requireBoolParam p = typeError $ "Expecting Bool, found " ++ show p

requirePtrParam :: Show a => ParamType' a -> TypeCheck BaseType
requirePtrParam (PtrParam _ ty) = pure ty
requirePtrParam p = typeError $ "Expecting Ptr _, found " ++ show p

requireTypeP :: (HasCallStack, Show a, Eq a) => ParamType' a -> ParamType' a -> TypeCheck ()
requireTypeP (PtrParam _ ty) (PtrParam _ ty')
  | ty' == ty = pure ()
  | otherwise = typeError $ "Expected Ptr " ++ show ty ++ ", found Ptr " ++ show ty'
requireTypeP BoolParam{} BoolParam{} = pure ()
requireTypeP IntParam{} IntParam{} = pure ()
requireTypeP (LayoutParam x) (LayoutParam y)
  | x == y = pure ()
requireTypeP x y = typeError $ "Expected " ++ show x ++ ", found " ++ show y

checkExpr :: TcEnv -> Parsed ExprX String -> ParamType -> TypeCheck (Elaborated ExprX String)
checkExpr gamma e0@(Deref {}) ty = do
  (ty', e') <- inferExpr gamma e0
  requireBaseType ty
  pure e'

checkExpr gamma e0@(Addr {}) ty = do
  (ty', e') <- inferExpr gamma e0
  requireTypeP ty ty'
  pure e'

checkExpr gamma (IfThenElse () c t f) ty = do
  c' <- checkExpr gamma c (BoolParam Nothing)

  t' <- checkExpr gamma t ty
  f' <- checkExpr gamma f ty

  -- TODO: Should the out variables be combined?

  pure (IfThenElse ty c' t' f')

checkExpr gamma e@(Var {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireTypeP ty ty'
  pure e'

checkExpr gamma (IntLit i) ty = do
  requireIntParam ty
  pure $ (IntLit i)

checkExpr gamma (BoolLit b) ty = do
  requireBoolParam ty
  pure $ (BoolLit b)

checkExpr gamma e@(And {}) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Or {}) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Not {}) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Add {}) ty = do
  requireIntParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Sub {}) ty = do
  requireIntParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Mul {}) ty = do
  requireIntParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Equal x y) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Le x y) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Lt x y) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure e'

checkExpr gamma e@(Instantiate inLayoutNames outLayoutName f args) ty = do
  (ty', e') <- inferExpr gamma e
  requireTypeP ty ty'
  pure e'

checkExpr gamma e@(Lower {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireTypeP ty ty'
  pure e'

checkExpr gamma e@(ConstrApply {}) ty =
  typeError $
    unlines
    [ "Found un-lowered constructor application " ++ show e
    , "Expected concrete type " ++ show ty
    ]

checkExpr gamma e@(Apply {}) ty =
  typeError $
    unlines
    [ "Found un-instantiated function application " ++ show e
    , "Expected concrete type " ++ show ty
    ]

checkExpr gamma e@(LetIn () v rhs body) ty = do
  (tyV, rhs') <- inferExpr gamma rhs
  checkExpr ((v, tyV) : gamma) body ty

requireBaseType :: Show a => ParamType' a -> TypeCheck (BaseType, ParamType' a)
requireBaseType (IntParam v) = pure (IntBase, PtrParam (fmap Here v) IntBase)
requireBaseType (BoolParam v) = pure (BoolBase, PtrParam (fmap Here v) BoolBase)
requireBaseType p = typeError $ "Expected base type, found " ++ show p

inferExpr :: TcEnv -> Parsed ExprX String -> TypeCheck (ParamType, ElaboratedExpr String)
inferExpr gamma (Var () v) =
  case lookup v gamma of
    Nothing -> error $ "inferExpr: variable not found in TcEnv: " ++ v ++ "\nTcEnv = " ++ show gamma ++ "\n"
    Just ty -> do
      layouts <- getLayouts
      pure (ty, Var ty v)

inferExpr gamma (Deref () e) = do
  (ty0, e') <- inferExpr gamma e
  baseTy <- requirePtrParam ty0
  let ty' = case baseTy of
             IntBase -> IntParam Nothing
             BoolBase -> BoolParam Nothing

  pure (ty', Addr ty' e')

inferExpr gamma (Addr () e@(Var () v)) = do
  (ty0, e') <- inferExpr gamma e
  (baseTy, paramTy) <- requireBaseType ty0
  let ty' = PtrParam (Just (Here v)) baseTy

  pure (ty', Addr ty' e')

inferExpr gamma (IntLit i) = do
  pure (IntParam Nothing, IntLit i)

inferExpr gamma (BoolLit b) = do
  pure (BoolParam Nothing, BoolLit b)

inferExpr gamma (And x y) = do
  x' <- checkExpr gamma x (BoolParam Nothing)
  y' <- checkExpr gamma y (BoolParam Nothing)
  pure $ (BoolParam Nothing, And x' y')

inferExpr gamma (Or x y) = do
  x' <- checkExpr gamma x (BoolParam Nothing)
  y' <- checkExpr gamma y (BoolParam Nothing)
  pure $ (BoolParam Nothing, Or x' y')

inferExpr gamma (Not x) = do
  x' <- checkExpr gamma x (BoolParam Nothing)
  pure $ (BoolParam Nothing, Not x')

inferExpr gamma (Add x y) = do
  x' <- checkExpr gamma x (IntParam Nothing)
  y' <- checkExpr gamma y (IntParam Nothing)
  pure $ (IntParam Nothing, Add x' y')

inferExpr gamma (Sub x y) = do
  x' <- checkExpr gamma x (IntParam Nothing)
  y' <- checkExpr gamma y (IntParam Nothing)
  pure $ (IntParam Nothing, Sub x' y')

inferExpr gamma (Mul x y) = do
  x' <- checkExpr gamma x (IntParam Nothing)
  y' <- checkExpr gamma y (IntParam Nothing)
  pure $ (IntParam Nothing, Mul x' y')

inferExpr gamma (Equal x y) = do
  x' <- checkExpr gamma x (IntParam Nothing)
  y' <- checkExpr gamma y (IntParam Nothing)
  pure $ (BoolParam Nothing, Equal x' y')

inferExpr gamma (Le x y) = do
  x' <- checkExpr gamma x (IntParam Nothing)
  y' <- checkExpr gamma y (IntParam Nothing)
  pure $ (BoolParam Nothing, Le x' y')

inferExpr gamma (Lt x y) = do
  x' <- checkExpr gamma x (IntParam Nothing)
  y' <- checkExpr gamma y (IntParam Nothing)
  pure $ (BoolParam Nothing, Lt x' y')

inferExpr gamma e0@(Instantiate inTys outTy f args) = do
  if length args /= length inTys
    then typeError $ "Wrong number of arguments. Expected " ++ show (length inTys) ++ ", found " ++ show (length args) ++ " in: " ++ show e0
    else pure ()

  def <- lookupDefM f

  args' <-
    sequenceA $
      zipWith
        (checkExpr gamma)
        args
        inTys

  pure $ (outTy
         ,
          Apply
            f
            outTy
            inTys
            args'
         )

inferExpr gamma (Lower layoutName (Var () v)) = do
  inferExpr gamma (Var () v)
    -- TODO: Does this need a copy (so, a different out var)?

inferExpr gamma (Lower ty (ConstrApply () cName args)) = do
    -- TODO: Check that the ADT matches the layout

  foundTy <- lookupParamType ty

  argsWithTys <- traverse (inferWith gamma ty) args

  pure $ (ty, ConstrApply ty cName (map snd argsWithTys))

inferExpr gamma e@(Lower {}) =
  typeError $ "'lower' expression with incorrect form. Should be of the form 'lower v' or 'lower (C ...)'. Found: " ++ show e

inferExpr gamma e@(ConstrApply {}) =
  typeError $ "Un-lowered constructor application: " ++ show e

inferExpr gamma e@(Apply {}) =
  typeError $ "Un-instantiated function application: " ++ show e

inferExpr gamma (LetIn () v rhs body) = do
  (ty, rhs') <- inferExpr gamma rhs
  (ty2, body2) <- inferExpr ((v, updateParams [v] ty) : gamma) body

  pure $ (ty2, LetIn ty2 v rhs' body2)

inferExpr gamma (IfThenElse () c t f) = do
  c' <- checkExpr gamma c (BoolParam Nothing)
  (ty1, t') <- inferExpr gamma t
  (ty2, f') <- inferExpr gamma f
  requireTypeP ty1 ty2
  -- TODO: Do we need to combine the names of ty1 and ty2 (possibly using
  -- LetIn)?
  pure (ty1, IfThenElse ty1 c' t' f')

