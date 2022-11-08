--
-- Basic type checking and elaboration
--
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

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

import Debug.Trace

-- elaborateExpr :: [Layout] -> [Parsed Def] -> Parsed ExprX a -> Elaborated ExprX a
-- elaborateExpr layouts defs = undefined

data TcGlobals = MkTcGlobals [Layout] [Adt] [Parsed (Def ())]

data OutVar = InitialOutVar | SubOutVar

type OutParams = [String]

newtype TypeCheck a = MkTypeCheck (ReaderT TcGlobals (StateT OutVar (FreshGenT (Either String))) a)
  deriving (Functor, Applicative, Monad, MonadReader TcGlobals, MonadState OutVar)

instance MonadFail TypeCheck where
  fail = error

runTypeCheck :: [Layout] -> [Adt] -> [Parsed (Def ())] -> TypeCheck a -> a
runTypeCheck layouts adts defs (MkTypeCheck tc) =
  let globals = MkTcGlobals layouts adts defs
  in
  case runFreshGenT $ flip evalStateT InitialOutVar $ runReaderT tc globals of
    Left err -> error err
    Right (_, x) -> x

type TcEnv = [(String, ParamType)]

lookupLayoutM :: String -> TypeCheck Layout
lookupLayoutM name = do
  MkTcGlobals layouts _ _ <- ask
  pure $ lookupLayout layouts name

type ParamTypeL = ParamType' Layout

lookupParamType :: ParamType -> TypeCheck ParamTypeL
lookupParamType IntParam = pure IntParam
lookupParamType BoolParam = pure BoolParam
lookupParamType (LayoutParam layoutName) = LayoutParam <$> lookupLayoutM (baseLayoutName layoutName)

lookupAdtM :: String -> TypeCheck Adt
lookupAdtM name = do
  MkTcGlobals _ adts _ <- ask
  pure $ lookupAdt adts name

lookupDefM :: String -> TypeCheck (Parsed (Def ()))
lookupDefM name = do
  MkTcGlobals _ _ defs <- ask
  pure $ lookupDef defs name

genLayoutParamsWith :: String -> Layout -> TypeCheck [String]
genLayoutParamsWith prefix layout = do
  mapM (MkTypeCheck . lift . lift . getFreshWith . (prefix <>))
  $ layoutSuSLikParams layout

genLayoutParams :: Layout -> TypeCheck [String]
genLayoutParams = genLayoutParamsWith ""

genParamsWith :: String -> ParamTypeL -> TypeCheck [String]
genParamsWith prefix IntParam = fmap (:[]) . MkTypeCheck . lift . lift $ getFreshWith prefix
genParamsWith prefix BoolParam = fmap (:[]) . MkTypeCheck . lift . lift $ getFreshWith prefix
genParamsWith prefix (LayoutParam layout) = genLayoutParamsWith prefix layout

genParams :: ParamTypeL -> TypeCheck [String]
genParams = genParamsWith ""

initialOutParams :: ParamTypeL -> OutParams
initialOutParams (LayoutParam layout) =
  map ("__r_" <>) $ layoutSuSLikParams layout
initialOutParams _ = ["__r"]

newOutVars :: ParamTypeL -> TypeCheck OutParams
newOutVars ty =
  get >>= \case
    InitialOutVar -> put SubOutVar *> pure (initialOutParams ty)
    SubOutVar -> genParams ty

typeError :: String -> TypeCheck a
typeError err = MkTypeCheck . lift . lift . lift $ Left err

-- genLoweredType :: Int -> String -> LoweredType
-- genLoweredType count name =
--   MkLoweredType (map go [0..count]) $ LayoutConcrete $ MkLayoutName (Just Output) name
--   where
--     go n = name <> "__" <> show n

genLoweredType :: Layout -> TypeCheck LoweredType
genLoweredType layout = do
  params <- genLayoutParams layout
  pure $ MkLowered params $ MkLayoutName (Just Output) (layoutName layout) -- TODO: Is this mode correct?

-- toLoweredType :: String -> ConcreteType -> TypeCheck (String, LoweredType)
-- toLoweredType v ty@(MkLowered _ layoutName) = do
--     layout <- lookupLayoutM (baseLayoutName layoutName)
--
--     params <- genLayoutParams layout
--
--     -- let params = map go $ layoutSuSLikParams layout
--
--     pure (v, MkLowered params layoutName)
--   -- where
--   --   go n = v <> "__" <> n
-- toLoweredType v ty = pure (v, MkLowered [v] ty)

typeMatchesLowered :: Type -> LoweredType -> TypeCheck ()
typeMatchesLowered = go
  where
    go IntType IntConcrete = pure ()
    go BoolType BoolConcrete = pure ()
    go (AdtType name) _ = typeError $ "ADT type not lowered: " ++ name
    go (LayoutType name arity)
       (MkLowered params name') =
         if genLayoutName name' /= name
           then typeError $ "Expected layout " ++ name ++ " found " ++ genLayoutName name'
           else
             if arity /= length params
               then typeError $ "Expected " ++ show arity ++ " arguments to layout " ++ name ++ ", found " ++ show (length params)
               else pure ()
    go (LayoutType name _) lowered =
      typeError $ "Expected layout type, found " ++ show lowered
    go ty lowered =
      typeError $ "Expected " ++ show ty ++ ", found " ++ show lowered

requireType :: (Eq a, Show a) => a -> a -> TypeCheck ()
requireType expected found =
  if expected == found
    then pure ()
    else typeError $ "Expected type " ++ show expected ++ ", found " ++ show found

-- | Get the predicate name for a function with the given layouts
getPredName :: String -> [String] -> String -> String
getPredName fnName argLayouts resultLayout =
  fnName <> "__" <> intercalate "__" (resultLayout : argLayouts)

-- Also updates the Def name
instAndElaborate :: String -> [ParamType] -> ParamType -> ParsedDef -> TypeCheck ElaboratedDef
instAndElaborate fnName argParamTypes outParamType def = do
  let oldName = defName def
  elaborated <- elaborateDef argParamTypes outParamType
                  $ instDefCalls argParamTypes outParamType def
  pure $ elaborated
    { defName = (getPredName oldName (map genParamTypeName argParamTypes) (genParamTypeName outParamType))
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

paramTypeToLayout :: ParamTypeL -> Maybe Layout
paramTypeToLayout (LayoutParam layout) = Just layout
paramTypeToLayout _ = Nothing

-- paramTypeToConcrete :: ParamTypeL


elaborateDef :: [ParamType] -> ParamType -> ParsedDef -> TypeCheck (ElaboratedDef)
elaborateDef inParamTypes outParamType def = do
  foundArgTypes <- mapM lookupParamType inParamTypes
  argAdts <- mapM (traverse (lookupAdtM . layoutAdtName)) (map paramTypeToLayout foundArgTypes)
  foundOutType <- lookupParamType outParamType
  -- outLayout <- lookupLayoutM (baseLayoutName outParamType)

  argParams <- mapM genParams foundArgTypes

  let outParams = initialOutParams foundOutType --genLayoutParamsWith "out_" outLayout

  let paramedLayouts = zipWith mkParamTypeP argParams inParamTypes


  let goBranch :: ParsedDefBranch -> TypeCheck ElaboratedDefBranch
      goBranch defBranch = do
          let gamma = concat $ zipWith3 inferLayoutPatVars foundArgTypes argAdts $ defBranchPatterns defBranch


          let goGuarded (MkGuardedExpr x y) = do
                put InitialOutVar

                MkGuardedExpr <$> goExpr x <*> goExpr y

              goExpr e = do
                (_, e') <- inferWith gamma outParamType e
                pure e'

          guardeds <- mapM goGuarded (defBranchGuardeds defBranch)

          pure $ defBranch
            { defBranchPatterns = zipWith elaboratePattern (defBranchPatterns defBranch) paramedLayouts
            , defBranchGuardeds = guardeds
            }
          --
  defBranches' <- mapM (defParamSubst paramedLayouts <=< goBranch) (defBranches def)

  pure $ def
    { defBranches = defBranches'
    , defType = (paramedLayouts, mkParamTypeP outParams outParamType)
    }

-- | Substitute the SuSLik parameters for any PatternVar into the appropriate place in the
-- given expressions.
defParamSubst :: [ParamTypeP] -> ElaboratedDefBranch -> TypeCheck ElaboratedDefBranch
defParamSubst params branch = do
  subst <- catMaybes <$> mapM (uncurry genPatParamSubst) (zip params (defBranchPatterns branch))

  let go guarded = applyPatParamSubst subst guarded

  pure $ branch
    { defBranchGuardeds = map go $ defBranchGuardeds branch
    }

genPatParamSubst :: ParamTypeP -> Pattern' ParamTypeP -> TypeCheck (Maybe (String, [String]))
genPatParamSubst IntParam (PatternVar params v) = pure $ Just (v, loweredParams params)
genPatParamSubst BoolParam (PatternVar params v) = pure $ Just (v, loweredParams params)
genPatParamSubst LayoutParam{} (PatternVar params v) = pure $ Just (v, loweredParams params)
genPatParamSubst _ _ = pure Nothing

applyPatParamSubst :: [(String, [String])] -> Elaborated GuardedExpr -> Elaborated GuardedExpr
applyPatParamSubst subst (MkGuardedExpr x y) =
  MkGuardedExpr (go x) (go y)
  where
    go :: ElaboratedExpr String -> ElaboratedExpr String
    go e0@(Var ty v) =
      case lookup v subst of
        Just params -> Var (withParams params (fmap getParamedName ty)) v
        Nothing -> e0
    go e0@(IntLit {}) = e0
    go e0@(BoolLit {}) = e0
    go (And x y) = And (go x) (go y)
    go (Or x y) = Or (go x) (go y)
    go (Not x) = Not (go x)
    go (Add x y) = Add (go x) (go y)
    go (Sub x y) = Sub (go x) (go y)
    go (Mul x y) = Mul (go x) (go y)
    go (Equal x y) = Equal (go x) (go y)
    go (Le x y) = Le (go x) (go y)
    go (Lt x y) = Lt (go x) (go y)
    go (Apply f outTy inTys args) =
      Apply f outTy inTys (map go args)
    go (ConstrApply ty cName args) =
      ConstrApply ty cName (map go args)
    go Lower{} = error "go: Lower (impossible)"
    go Instantiate{} = error "go: Instantiate (impossible)"


elaboratePattern :: Pattern -> ParamTypeP -> Pattern' ParamTypeP
elaboratePattern pat x = patternSet x pat
-- elaboratePattern pat _ = pat

inferLayoutPatVars :: ParamTypeL -> Maybe Adt -> Pattern -> [(FsName, ParamType)]
inferLayoutPatVars BoolParam _ (PatternVar _ v) = [(v, BoolParam)]
inferLayoutPatVars IntParam _ (PatternVar _ v) = [(v, IntParam)]
inferLayoutPatVars BoolParam _ pat = error $ "Attempt to pattern match on Bool: " ++ show pat
inferLayoutPatVars IntParam _ pat = error $ "Attempt to pattern match on Int: " ++ show pat
inferLayoutPatVars (LayoutParam layout) (Just adt) (PatternVar _ v) = [(v, LayoutParam (MkLayoutName (Just Input) (layoutName layout)))]
inferLayoutPatVars (LayoutParam layout) (Just adt) pat@(MkPattern _ cName params) =
    let adtFields = adtBranchFields $ findAdtBranch adt cName
    in
    zipWith go params adtFields
  where
    -- appliedLayout = applyLayoutPat layout [] pat

    go v IntType = (v, IntParam)
    go v BoolType = (v, BoolParam)
    go v _ = (v, LayoutParam $ findLayoutApp v $ snd $ lookupLayoutBranch layout cName)
    -- go v _ = (v, LayoutConcrete $ findLayoutApp v appliedLayout)
inferLayoutPatVars (LayoutParam layout) Nothing _ = error $ "inferLayoutPatVars: Could not find ADT associated to layout " ++ show layout

findLayoutApp :: FsName -> Assertion FsName -> LayoutName
findLayoutApp v = go
  where
    go :: Assertion FsName -> LayoutName
    go Emp = error $ "findLayoutApp: Cannot find " ++ show v
    go (PointsTo _ _ _ rest) = go rest
    go (HeapletApply lName params [Var _ v'] rest)
      | v' == v = lName
      | otherwise = go rest
    go (HeapletApply lName params _ rest) = go rest

inferWith :: TcEnv -> ParamType -> Parsed ExprX String -> TypeCheck (ParamTypeP, Elaborated ExprX String)
inferWith gamma ty@(LayoutParam layout) e@(ConstrApply {}) =
  -- inferExpr gamma (Lower (MkLayoutName (Just Input) (layoutName layout)) e)
  inferExpr gamma (Lower ty e)
inferWith _ ty e@(ConstrApply {}) = error $ "Constructor application of non-layout type:\nType = " ++ show ty ++ "\nExpr = " ++ show e ++ "\n"
inferWith gamma layout e = inferExpr gamma e

checkExpr :: TcEnv -> Parsed ExprX String -> ParamType -> TypeCheck (OutParams, Elaborated ExprX String)
checkExpr gamma e@(Var {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireType ty $ fmap getParamedName ty'
  pure (loweredParams ty', e')

checkExpr gamma (IntLit i) ty = do
  requireType ty IntParam
  pure $ ([], IntLit i)

checkExpr gamma (BoolLit b) ty = do
  requireType ty BoolParam
  pure $ ([], BoolLit b)

checkExpr gamma e@(And {}) ty = do
  requireType ty BoolParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Or {}) ty = do
  requireType ty BoolParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Not {}) ty = do
  requireType ty BoolParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Add {}) ty = do
  requireType ty IntParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Sub {}) ty = do
  requireType ty IntParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Mul {}) ty = do
  requireType ty IntParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Equal x y) ty = do
  requireType ty BoolParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Le x y) ty = do
  requireType ty BoolParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Lt x y) ty = do
  requireType ty BoolParam
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Instantiate inLayoutNames outLayoutName f args) ty = do
  (ty', e') <- inferExpr gamma e
  requireType ty $ fmap getParamedName ty'
  pure (loweredParams ty', e')

checkExpr gamma e@(Lower {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireType ty $ fmap getParamedName ty'
  pure (loweredParams ty', e')

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

inferExpr :: TcEnv -> Parsed ExprX String -> TypeCheck (ParamTypeP, Elaborated ExprX String)
inferExpr gamma (Var () v) =
  case lookup v gamma of
    Nothing -> error $ "inferExpr: variable not found in TcEnv: " ++ v ++ "\nTcEnv = " ++ show gamma ++ "\n"
    Just concTy -> do
      -- typeMatchesLowered ty lowered
      -- requireType ty (loweredType lowered)

      let lowered = withParams [v] concTy
      pure $ (lowered, Var lowered v)
inferExpr gamma (IntLit i) = do
  pure (IntParam, IntLit i)

inferExpr gamma (BoolLit b) = do
  pure (BoolParam, BoolLit b)

inferExpr gamma (And x y) = do
  ([], x') <- checkExpr gamma x BoolParam
  ([], y') <- checkExpr gamma y BoolParam
  pure $ (BoolParam, And x' y')

inferExpr gamma (Or x y) = do
  ([], x') <- checkExpr gamma x BoolParam
  ([], y') <- checkExpr gamma y BoolParam
  pure $ (BoolParam, Or x' y')

inferExpr gamma (Not x) = do
  ([], x') <- checkExpr gamma x BoolParam
  pure $ (BoolParam, Not x')

inferExpr gamma (Add x y) = do
  ([], x') <- checkExpr gamma x IntParam
  ([], y') <- checkExpr gamma y IntParam
  pure $ (IntParam, Add x' y')

inferExpr gamma (Sub x y) = do
  ([], x') <- checkExpr gamma x IntParam
  ([], y') <- checkExpr gamma y IntParam
  pure $ (IntParam, Sub x' y')

inferExpr gamma (Mul x y) = do
  ([], x') <- checkExpr gamma x IntParam
  ([], y') <- checkExpr gamma y IntParam
  pure $ (IntParam, Mul x' y')

inferExpr gamma (Equal x y) = do
  ([], x') <- checkExpr gamma x IntParam
  ([], y') <- checkExpr gamma y IntParam
  pure $ (BoolParam, Equal x' y')

inferExpr gamma (Le x y) = do
  ([], x') <- checkExpr gamma x IntParam
  ([], y') <- checkExpr gamma y IntParam
  pure $ (BoolParam, Le x' y')

inferExpr gamma (Lt x y) = do
  ([], x') <- checkExpr gamma x IntParam
  ([], y') <- checkExpr gamma y IntParam
  pure $ (BoolParam, Lt x' y')

inferExpr gamma e0@(Instantiate inLayoutNames outLayoutName f args) = do
  if length args /= length inLayoutNames
    then typeError $ "Wrong number of arguments. Expected " ++ show (length inLayoutNames) ++ ", found " ++ show (length args) ++ " in: " ++ show e0
    else pure ()

  args' <-
    sequenceA $
      zipWith
        (checkExpr gamma)
        args
        inLayoutNames

  def <- lookupDefM f

  outLayout <- lookupParamType outLayoutName
  -- let outLayoutParams = layoutSuSLikParams outLayout

  -- loweredTy <- genLoweredType outLayout

  outVars <- newOutVars outLayout

  -- let loweredTy = MkLowered outVars outLayoutName

  outParams <- genParams outLayout

  -- loweredOutTy <- lowerParamType outLayoutName
  -- argTys <- mapM lowerParamType inLayoutNames

  argLayouts <- mapM lookupParamType inLayoutNames
  argParams <- mapM genParams argLayouts


  pure $ (fmap (MkParametrizedLayoutName outParams) outLayoutName
         ,
          Apply
            (getPredName f (map genParamTypeName inLayoutNames) (genParamTypeName outLayoutName)) -- Name
            (mkParamTypeP outParams outLayoutName) -- Output layout
            (zipWith mkParamTypeP argParams inLayoutNames)
            -- (zipWith MkLowered (map fst args') inLayoutNames)
            (map snd args') -- fun-SuSLik args
         )

inferExpr gamma (Lower layoutName (Var () v)) = do
  -- requireType ty $ LayoutConcrete layoutName
  inferExpr gamma (Var () v)
    -- TODO: Does this need a copy (so, a different out var)?

inferExpr gamma (Lower ty (ConstrApply () cName args)) = do
    -- TODO: Check that the ADT matches the layout

  foundTy <- lookupParamType ty

  -- ty'' <- genLoweredType layout

  -- outVars <- newOutVars layout
  -- let ty'' = MkLowered outVars layoutName

  -- ty'' <- lowerParamType layoutName

  argsWithTys <- traverse (inferWith gamma ty) args

  params <- newOutVars foundTy

  let paramTy = mkParamTypeP params ty

  pure $ (paramTy, ConstrApply paramTy cName (map snd argsWithTys))

inferExpr gamma e@(Lower {}) =
  typeError $ "'lower' expression with incorrect form. Should be of the form 'lower v' or 'lower (C ...)'. Found: " ++ show e

inferExpr gamma e@(ConstrApply {}) =
  typeError $ "Un-lowered constructor application: " ++ show e

inferExpr gamma e@(Apply {}) =
  typeError $ "Un-instantiated function application: " ++ show e

lowerParamType ty = do
  foundTy <- lookupParamType ty
  params <- genParams foundTy
  case ty of
    LayoutParam layoutName -> pure $ MkLowered params layoutName
    IntParam -> pure IntConcrete
    BoolParam -> pure BoolConcrete

