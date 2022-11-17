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

-- elaborateExpr :: [Layout] -> [Parsed Def] -> Parsed ExprX a -> Elaborated ExprX a
-- elaborateExpr layouts defs = undefined

data TcGlobals = MkTcGlobals String [Layout] [Adt] [Parsed (Def ())]

data OutVar = InitialOutVar | SubOutVar
  deriving (Show)

type OutParams = [String]

newtype TypeCheck a = MkTypeCheck (ReaderT TcGlobals (StateT OutVar (FreshGenT (Either String))) a)
  deriving (Functor, Applicative, Monad, MonadReader TcGlobals, MonadState OutVar)

instance MonadFail TypeCheck where
  fail = error

runTypeCheck :: String -> [Layout] -> [Adt] -> [Parsed (Def ())] -> TypeCheck a -> a
runTypeCheck fnName layouts adts defs (MkTypeCheck tc) =
  let globals = MkTcGlobals fnName layouts adts defs
  in
  case runFreshGenT $ flip evalStateT InitialOutVar $ runReaderT tc globals of
    Left err -> error err
    Right (_, x) -> x

type TcEnv = [(String, ParamTypeP)]

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

genLayoutParamsWith :: String -> Layout -> TypeCheck [String]
genLayoutParamsWith prefix layout = do
  mapM (MkTypeCheck . lift . lift . getFreshWith . (prefix <>))
  $ layoutSuSLikParams layout

genLayoutParams :: Layout -> TypeCheck [String]
genLayoutParams = genLayoutParamsWith ""

genParamsWith :: String -> ParamTypeL -> TypeCheck [String]
genParamsWith prefix (PtrParam (Just v) ty) = pure [getLocBase v]
genParamsWith prefix (IntParam (Just v)) = pure [v]
genParamsWith prefix (BoolParam (Just v)) = pure [v]
genParamsWith prefix (PtrParam Nothing _) = fmap (:[]) . MkTypeCheck . lift . lift $ getFreshWith prefix
genParamsWith prefix (IntParam Nothing) = fmap (:[]) . MkTypeCheck . lift . lift $ getFreshWith prefix
genParamsWith prefix (BoolParam Nothing) = fmap (:[]) . MkTypeCheck . lift . lift $ getFreshWith prefix
genParamsWith prefix (LayoutParam layout) = genLayoutParamsWith prefix layout

genParams :: ParamTypeL -> TypeCheck [String]
genParams = genParamsWith "__p_"

genTemp :: String -> TypeCheck String
genTemp str = MkTypeCheck . lift . lift $ getFreshWith ("__tc_temp_" <> str)

initialOutParams :: ParamTypeL -> OutParams
initialOutParams (LayoutParam layout) =
  map ("__r_" <>) $ layoutSuSLikParams layout
initialOutParams _ = ["__r"]

newOutVars :: ParamTypeL -> TypeCheck OutParams
newOutVars ty =
  get >>= \case
    InitialOutVar -> put SubOutVar *> pure (initialOutParams ty)
    SubOutVar -> genParams ty

setSubexprOutVarState :: TypeCheck ()
setSubexprOutVarState = put SubOutVar

subexprStateBlock :: TypeCheck a -> TypeCheck a
subexprStateBlock m = do
  oldState <- get
  setSubexprOutVarState
  r <- m
  put oldState
  pure r


resetOutVarState :: TypeCheck ()
resetOutVarState = put InitialOutVar

typeError :: HasCallStack => String -> TypeCheck a
typeError err = error err --MkTypeCheck . lift . lift . lift $ Left err

-- genLoweredType :: Int -> String -> LoweredType
-- genLoweredType count name =
--   MkLoweredType (map go [0..count]) $ LayoutConcrete $ MkLayoutName (Just Output) name
--   where
--     go n = name <> "__" <> show n

genLoweredType :: Layout -> TypeCheck LoweredType
genLoweredType layout = do
  params <- genLayoutParams layout
  pure $ MkLowered (map Here params) $ MkLayoutName (Just Output) (layoutName layout) -- TODO: Is this mode correct?

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

elaborateDef :: [ParamType] -> ParamType -> ParsedDef -> TypeCheck (ElaboratedDef)
elaborateDef inParamTypes outParamType def = do
  foundArgTypes <- mapM lookupParamType inParamTypes
  argAdts <- mapM (traverse (lookupAdtM . layoutAdtName)) (map paramTypeToLayout foundArgTypes)
  foundOutType <- lookupParamType outParamType
  -- outLayout <- lookupLayoutM (baseLayoutName outParamType)

  argParams <- mapM genParams foundArgTypes

  let outParams = initialOutParams foundOutType --genLayoutParamsWith "out_" outLayout

  let paramedLayouts = zipWith mkParamTypeP argParams inParamTypes
  -- traceM ("argParams = " ++ show argParams)
  -- traceM ("inParamTypes = " ++ show inParamTypes)
  -- traceM ("paramedLayouts = " ++ show paramedLayouts)


  let goBranch :: ParsedDefBranch -> TypeCheck ElaboratedDefBranch
      goBranch defBranch = do
          -- () <- traceM $ "foundArgTypes = " ++ show foundArgTypes
          -- () <- traceM $ "defBranchPatterns = " ++ show (defBranchPatterns defBranch)
          let gamma0 = zipWith3 inferLayoutPatVars foundArgTypes argAdts $ defBranchPatterns defBranch

              goGamma :: [String] -> [(Pattern, (FsName, ParamType))] -> [(FsName, ParamTypeP)]
              goGamma vs = map (\(pat, xs) ->
                if isPatternVar pat
                  then second (mkParamTypeP vs) xs
                  else (fst xs, mkParamTypeP [fst xs] (snd xs)))

              gamma = concat $ zipWith goGamma argParams gamma0


          let goGuarded (MkGuardedExpr x y) = do
                MkGuardedExpr <$> goExpr x <*> goExpr y

              goExpr e = do
                resetOutVarState
                st <- get
                (_, e') <- inferWith gamma outParamType e
                pure e'

          -- () <- traceM $ "gamma0 = " ++ show gamma0
          -- () <- traceM $ "gamma = " ++ show gamma
          guardeds <- mapM (\x -> goGuarded x) (defBranchGuardeds defBranch)

          pure $ defBranch
            { defBranchPatterns = zipWith elaboratePattern (defBranchPatterns defBranch) paramedLayouts
            , defBranchGuardeds = guardeds
            }
          --
  -- defBranches' <- mapM (defParamSubst paramedLayouts <=< goBranch) (defBranches def)
  defBranches' <- mapM goBranch (defBranches def)

  pure $ def
    { defBranches = defBranches'
    , defType = (paramedLayouts, mkParamTypeP outParams outParamType)
    }

-- -- | Substitute the SuSLik parameters for any PatternVar into the appropriate place in the
-- -- given expressions.
-- defParamSubst :: [ParamTypeP] -> ElaboratedDefBranch -> TypeCheck ElaboratedDefBranch
-- defParamSubst params branch = do
--   subst <- catMaybes <$> mapM (uncurry genPatParamSubst) (zip params (defBranchPatterns branch))
--
--   let go guarded = applyPatParamSubst subst guarded
--
--   pure $ branch
--     { defBranchGuardeds = map go $ defBranchGuardeds branch
--     }
--
-- genPatParamSubst :: ParamTypeP -> Pattern' ParamTypeP -> TypeCheck (Maybe (String, [String]))
-- genPatParamSubst IntParam (PatternVar params v) = pure $ Just (v, loweredParams params)
-- genPatParamSubst BoolParam (PatternVar params v) = pure $ Just (v, loweredParams params)
-- genPatParamSubst LayoutParam{} (PatternVar params v) = pure $ Just (v, loweredParams params)
-- genPatParamSubst _ _ = pure Nothing
--
-- applyPatParamSubst :: [(String, [String])] -> Elaborated GuardedExpr -> Elaborated GuardedExpr
-- applyPatParamSubst subst (MkGuardedExpr x y) =
--   MkGuardedExpr (go x) (go y)
--   where
--     go :: ElaboratedExpr String -> ElaboratedExpr String
--     go e0@(Var ty v) =
--       case lookup v subst of
--         Just params -> Var (withParams params (fmap getParamedName ty)) v
--         Nothing -> e0
--     go e0@(IntLit {}) = e0
--     go e0@(BoolLit {}) = e0
--     go (And x y) = And (go x) (go y)
--     go (Or x y) = Or (go x) (go y)
--     go (Not x) = Not (go x)
--     go (Add x y) = Add (go x) (go y)
--     go (Sub x y) = Sub (go x) (go y)
--     go (Mul x y) = Mul (go x) (go y)
--     go (Equal x y) = Equal (go x) (go y)
--     go (Le x y) = Le (go x) (go y)
--     go (Lt x y) = Lt (go x) (go y)
--     go (Apply f outTy inTys args) =
--       Apply f outTy inTys (map go args)
--     go (ConstrApply ty cName args) =
--       ConstrApply ty cName (map go args)
--     go Lower{} = error "go: Lower (impossible)"
--     go Instantiate{} = error "go: Instantiate (impossible)"


elaboratePattern :: Pattern -> ParamTypeP -> Pattern' ParamTypeP
elaboratePattern pat x = patternSet x pat
-- elaboratePattern pat _ = pat

inferLayoutPatVars :: ParamTypeL -> Maybe Adt -> Pattern -> [(Pattern, (FsName, ParamType))]
inferLayoutPatVars (PtrParam p ty) _ pat@(PatternVar _ v) =
  [(pat, (v, PtrParam p ty))]
inferLayoutPatVars (BoolParam p) _ pat@(PatternVar _ v) = [(pat, (v, BoolParam p))]
inferLayoutPatVars (IntParam p) _ pat@(PatternVar _ v) = [(pat, (v, IntParam p))]
inferLayoutPatVars (BoolParam p) _ pat = error $ "Attempt to pattern match on Bool: " ++ show pat
inferLayoutPatVars (IntParam p) _ pat = error $ "Attempt to pattern match on Int: " ++ show pat
inferLayoutPatVars (LayoutParam layout) (Just adt) pat@(PatternVar _ v) = [(pat, (v, LayoutParam (MkLayoutName (Just Input) (layoutName layout))))]
inferLayoutPatVars (LayoutParam layout) (Just adt) pat@(MkPattern _ cName params) =
    let adtFields = adtBranchFields $ findAdtBranch adt cName
    in
    map (pat,) $ zipWith go params adtFields
  where
    appliedLayout = applyLayoutPat layout [] pat

    go v IntType = (v, IntParam $ Just v) -- TODO: Or should these be Nothing?
    go v BoolType = (v, BoolParam $ Just v)
    -- go v _ = (v, LayoutParam $ findLayoutApp v $ snd $ lookupLayoutBranch layout cName)
    -- go v (AdtType adtName) =
    --   (v, LayoutParam (MkLayoutName (Just Input) (layoutName layout))) -- TODO: Does this make sense?
    go v _ = (v, LayoutParam $ findLayoutApp v appliedLayout)
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

inferWith :: TcEnv -> ParamType -> Parsed ExprX String -> TypeCheck (ParamTypeP, Elaborated ExprX String)
inferWith gamma ty e = inferExpr gamma (lowerWith ty e)
-- inferWith gamma ty@(LayoutParam layout) e@(ConstrApply {}) =
--   -- inferExpr gamma (Lower (MkLayoutName (Just Input) (layoutName layout)) e)
--   inferExpr gamma (Lower ty e)
-- inferWith _ ty e@(ConstrApply {}) = error $ "Constructor application of non-layout type:\nType = " ++ show ty ++ "\nExpr = " ++ show e ++ "\n"
-- inferWith gamma layout e = inferExpr gamma e

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

checkExpr :: TcEnv -> Parsed ExprX String -> ParamType -> TypeCheck (OutParams, Elaborated ExprX String)
checkExpr gamma e0@(Deref {}) ty = do
  (ty', e') <- inferExpr gamma e0
  requireBaseType ty
  pure (loweredParams ty', e')

checkExpr gamma e0@(Addr {}) ty = do
  (ty', e') <- inferExpr gamma e0
  requireTypeP ty $ fmap getParamedName ty'
  pure (loweredParams ty', e')

checkExpr gamma (IfThenElse () c t f) ty = do
  (_, c') <- checkExpr gamma c (BoolParam Nothing)

  (out, t') <- inferExpr gamma t
  (_, f') <- inferExpr gamma f

  -- TODO: Should the out variables be combined?

  pure $ (loweredParams out, IfThenElse out c' t' f')

checkExpr gamma e@(Var {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireTypeP ty $ fmap getParamedName ty'
  pure (loweredParams ty', e')

checkExpr gamma (IntLit i) ty = do
  requireIntParam ty
  pure $ ([], IntLit i)

checkExpr gamma (BoolLit b) ty = do
  requireBoolParam ty
  pure $ ([], BoolLit b)

checkExpr gamma e@(And {}) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Or {}) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Not {}) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Add {}) ty = do
  requireIntParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Sub {}) ty = do
  requireIntParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Mul {}) ty = do
  requireIntParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Equal x y) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Le x y) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Lt x y) ty = do
  requireBoolParam ty
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Instantiate inLayoutNames outLayoutName f args) ty = do
  (ty', e') <- inferExpr gamma e
  requireTypeP ty $ fmap getParamedName ty'
  pure (loweredParams ty', e')

checkExpr gamma e@(Lower {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireTypeP ty $ fmap getParamedName ty'
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

checkExpr gamma e@(LetIn () v rhs body) ty = do
  (tyV, rhs') <- inferExpr gamma rhs
  checkExpr ((v, tyV) : gamma) body ty

requireBaseType :: Show a => ParamType' a -> TypeCheck (BaseType, ParamType' a)
requireBaseType (IntParam v) = pure (IntBase, PtrParam (fmap Here v) IntBase)
requireBaseType (BoolParam v) = pure (BoolBase, PtrParam (fmap Here v) BoolBase)
requireBaseType p = typeError $ "Expected base type, found " ++ show p

inferExpr :: TcEnv -> Parsed ExprX String -> TypeCheck (ParamTypeP, Elaborated ExprX String)
inferExpr gamma (Var () v) =
  -- trace ("gamma = " ++ show gamma) $
  -- trace ("inferring var " ++ show v) $
  case lookup v gamma of
    Nothing -> error $ "inferExpr: variable not found in TcEnv: " ++ v ++ "\nTcEnv = " ++ show gamma ++ "\n"
    Just concTy -> do
      layouts <- getLayouts
      r <- newOutVars (fmap (lookupLayout layouts . baseLayoutName . getParamedName) concTy)
      -- traceM ("concTy = " ++ show concTy)
      -- typeMatchesLowered ty lowered
      -- requireType ty (loweredType lowered)

      -- let lowered = withParams [v] concTy

      let lowered = concTy --withParams [v] concTy
      -- let lowered = overwriteParams r concTy

      -- pure $ (lowered, Var lowered v)
      let ps = loweredParams $ lowered
      let (p:_) = ps
      -- () <- traceM ("inferExpr: " ++ show (v, lowered, p))
      pure $ (lowered, Var lowered p)

inferExpr gamma (Deref () e) = do
  (ty0, e') <- inferExpr gamma e
  baseTy <- requirePtrParam ty0
  let ty' = case baseTy of
             IntBase -> IntParam Nothing
             BoolBase -> BoolParam Nothing

  pure (ty', Addr ty' e')

  -- (ty0, e') <- inferExpr gamma e
  -- (baseTy, paramTy) <- requireBaseType ty0
  -- let ty = case baseTy of
  --            IntBase -> IntParam Nothing
  --            BoolBase -> BoolParam Nothing
  -- pure (ty, Deref paramTy e')

inferExpr gamma (Addr () e@(Var () v)) = do
  (ty0, e') <- inferExpr gamma e
  (baseTy, paramTy) <- requireBaseType ty0
  let ty' = PtrParam (Just (Here v)) baseTy
  -- let ty' = PtrParam Nothing baseTy

  pure (ty', Addr ty' e')

  -- (ty0, e') <- inferExpr gamma e
  -- baseTy <- requirePtrParam ty0
  --
  -- let ty' = PtrParam undefined baseTy
  --
  -- pure (ty', Addr ty' e')
  --
inferExpr gamma (IntLit i) = do
  pure (IntParam Nothing, IntLit i)

inferExpr gamma (BoolLit b) = do
  pure (BoolParam Nothing, BoolLit b)

inferExpr gamma (And x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (BoolParam Nothing)
  (_, y') <- checkExpr gamma y (BoolParam Nothing)
  pure $ (BoolParam Nothing, And x' y')

inferExpr gamma (Or x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (BoolParam Nothing)
  (_, y') <- checkExpr gamma y (BoolParam Nothing)
  pure $ (BoolParam Nothing, Or x' y')

inferExpr gamma (Not x) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (BoolParam Nothing)
  pure $ (BoolParam Nothing, Not x')

inferExpr gamma (Add x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (IntParam Nothing)
  (_, y') <- checkExpr gamma y (IntParam Nothing)
  pure $ (IntParam Nothing, Add x' y')

inferExpr gamma (Sub x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (IntParam Nothing)
  (_, y') <- checkExpr gamma y (IntParam Nothing)
  pure $ (IntParam Nothing, Sub x' y')

inferExpr gamma (Mul x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (IntParam Nothing)
  (_, y') <- checkExpr gamma y (IntParam Nothing)
  pure $ (IntParam Nothing, Mul x' y')

inferExpr gamma (Equal x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (IntParam Nothing)
  (_, y') <- checkExpr gamma y (IntParam Nothing)
  pure $ (BoolParam Nothing, Equal x' y')

inferExpr gamma (Le x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (IntParam Nothing)
  (_, y') <- checkExpr gamma y (IntParam Nothing)
  pure $ (BoolParam Nothing, Le x' y')

inferExpr gamma (Lt x y) = do
  setSubexprOutVarState
  (_, x') <- checkExpr gamma x (IntParam Nothing)
  (_, y') <- checkExpr gamma y (IntParam Nothing)
  pure $ (BoolParam Nothing, Lt x' y')

inferExpr gamma e0@(Instantiate inLayoutNames outLayoutName f args) = do
  if length args /= length inLayoutNames
    then typeError $ "Wrong number of arguments. Expected " ++ show (length inLayoutNames) ++ ", found " ++ show (length args) ++ " in: " ++ show e0
    else pure ()

  def <- lookupDefM f

  outLayout <- lookupParamType outLayoutName

  -- st <- get
  -- traceM $ "\nst = " ++ show st

  -- outParams <- genParams outLayout
  outVars <- newOutVars outLayout

  args' <-
    sequenceA $
      zipWith
        (checkExpr gamma)
        args
        inLayoutNames

  -- currFn <- getCurrFnName

  -- () <- traceM $ "\nf       = " ++ f
  -- () <- traceM $ "args    = " ++ show args
  -- () <- traceM $ "outVars = " ++ show outVars
  -- () <- traceM $ "is currFn = " ++ show (f == currFn)


  -- let outLayoutParams = layoutSuSLikParams outLayout

  -- loweredTy <- genLoweredType outLayout


  -- let loweredTy = MkLowered outVars outLayoutName

  -- let outVars = outParams

  -- loweredOutTy <- lowerParamType outLayoutName
  -- argTys <- mapM lowerParamType inLayoutNames

  argLayouts <- mapM lookupParamType inLayoutNames
  argParams <- mapM genParams argLayouts

  let ty' = fmap (MkParametrizedLayoutName (map Here outVars)) outLayoutName

  pure $ (ty'
         ,
          Apply
            (getPredName f (map genParamTypeName inLayoutNames) (genParamTypeName outLayoutName)) -- Name
            (mkParamTypeP outVars outLayoutName) -- Output layout
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

  params <- newOutVars foundTy

  argsWithTys <- traverse (inferWith gamma ty) args

  let paramTy = mkParamTypeP params ty

  pure $ (paramTy, ConstrApply paramTy cName (map snd argsWithTys))

inferExpr gamma e@(Lower {}) =
  typeError $ "'lower' expression with incorrect form. Should be of the form 'lower v' or 'lower (C ...)'. Found: " ++ show e

inferExpr gamma e@(ConstrApply {}) =
  typeError $ "Un-lowered constructor application: " ++ show e

inferExpr gamma e@(Apply {}) =
  typeError $ "Un-instantiated function application: " ++ show e

inferExpr gamma (LetIn () v rhs body) = do
  (ty, rhs') <- subexprStateBlock $ inferExpr gamma rhs
  (ty2, body2) <- inferExpr ((v, updateParams [v] ty) : gamma) body

  -- v' <- genTemp v
  -- let ty2' = overwriteParams [v'] ty2 -- TODO: Is this the write way to overwrite here 

  pure $ (ty2, LetIn ty2 v rhs' body2)

inferExpr gamma (IfThenElse () c t f) = do
  (_, c') <- checkExpr gamma c (BoolParam Nothing)
  (ty1, t') <- inferExpr gamma t
  (ty2, f') <- inferExpr gamma f
  requireTypeP ty1 ty2
  -- TODO: Do we need to combine the names of ty1 and ty2 (possibly using
  -- LetIn)?
  pure (ty1, IfThenElse ty1 c' t' f')


-- lowerParamType ty = do
--   foundTy <- lookupParamType ty
--   params <- genParams foundTy
--   case ty of
--     LayoutParam layoutName -> pure $ MkLowered params layoutName
--     IntParam -> pure IntConcrete
--     BoolParam -> pure BoolConcrete

