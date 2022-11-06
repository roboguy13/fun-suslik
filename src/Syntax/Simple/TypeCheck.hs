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
import           Data.Void

import           Control.Monad.Reader
import           Control.Monad.State

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

type TcEnv = [(String, ConcreteType)]

lookupLayoutM :: String -> TypeCheck Layout
lookupLayoutM name = do
  MkTcGlobals layouts _ _ <- ask
  pure $ lookupLayout layouts name

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

initialOutLayoutParams :: Layout -> OutParams
initialOutLayoutParams =
  map ("__r_" <>) . layoutSuSLikParams

newOutVars :: Layout -> TypeCheck OutParams
newOutVars layout =
  get >>= \case
    InitialOutVar -> put SubOutVar *> pure (initialOutLayoutParams layout)
    SubOutVar -> genLayoutParams layout

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

instAndElaborate :: String -> [LayoutName] -> LayoutName -> ParsedDef -> TypeCheck ElaboratedDef
instAndElaborate fnName argLayoutNames outLayoutName def =
  elaborateDef argLayoutNames outLayoutName
    $ instDefCalls argLayoutNames outLayoutName def

instDefCalls :: [LayoutName] -> LayoutName -> ParsedDef -> ParsedDef
instDefCalls argLayoutNames outLayoutName def =
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

    go = instCall (defName def) argLayoutNames outLayoutName

-- | Any call to the given function gets surrounded by an instantiation with
-- the given layouts. This is useful for recursive calls.
-- If it encounters an application of the function that is instantiated
-- to different layouts, it leaves that instantiation unchanged.
instCall :: String -> [LayoutName] -> LayoutName -> Parsed ExprX String -> Parsed ExprX String
instCall fnName argLayoutNames outLayoutName = go
  where
    instantiate = Instantiate argLayoutNames outLayoutName fnName
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

elaborateDef :: [LayoutName] -> LayoutName -> ParsedDef -> TypeCheck (ElaboratedDef)
elaborateDef inLayoutNames outLayoutName def = do
  argLayouts <- mapM (lookupLayoutM . baseLayoutName) inLayoutNames
  argAdts <- mapM (lookupAdtM . layoutAdtName) argLayouts
  outLayout <- lookupLayoutM (baseLayoutName outLayoutName)

  argParams <- mapM genLayoutParams argLayouts
  outParams <- genLayoutParamsWith "out_" outLayout

  let goBranch defBranch = do
          let gamma = concat $ zipWith3 inferLayoutPatVars argLayouts argAdts $ defBranchPatterns defBranch


          let goGuarded (MkGuardedExpr x y) = do
                put InitialOutVar

                MkGuardedExpr <$> goExpr x <*> goExpr y

              goExpr e = do
                (_, e') <- inferWith gamma outLayout e
                pure e'

          guardeds <- mapM goGuarded (defBranchGuardeds defBranch)

          let paramedLayouts = zipWith MkParametrizedLayoutName argParams inLayoutNames

          pure $ defBranch
            { defBranchPatterns = zipWith elaboratePattern (defBranchPatterns defBranch) paramedLayouts
            , defBranchGuardeds = guardeds
            }
          --
  defBranches' <- mapM goBranch (defBranches def)

  pure $ def { defBranches = defBranches' }

elaboratePattern :: Pattern -> ParametrizedLayoutName -> PatternWithLayout
elaboratePattern = flip patternSet

inferLayoutPatVars :: Layout -> Adt -> Pattern -> [(FsName, ConcreteType)]
inferLayoutPatVars layout adt (PatternVar _ v) = [(v, LayoutConcrete (MkLayoutName (Just Input) (layoutName layout)))]
inferLayoutPatVars layout adt (MkPattern _ cName params) =
    let adtFields = adtBranchFields $ findAdtBranch adt cName
    in
    zipWith go params adtFields
  where
    go v IntType = (v, IntConcrete)
    go v BoolType = (v, BoolConcrete)
    go v _ = (v, LayoutConcrete $ findLayoutApp v $ lookupLayoutBranch layout cName)

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

inferWith :: TcEnv -> Layout -> Parsed ExprX String -> TypeCheck (LoweredType, Elaborated ExprX String)
inferWith gamma layout e@(ConstrApply {}) =
  inferExpr gamma (Lower (MkLayoutName (Just Input) (layoutName layout)) e)
inferWith gamma layout e = inferExpr gamma e

checkExpr :: TcEnv -> Parsed ExprX String -> ConcreteType -> TypeCheck (OutParams, Elaborated ExprX String)
checkExpr gamma e@(Var {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireType ty $ forgetParams ty'
  pure (loweredParams ty', e')

checkExpr gamma (IntLit i) ty = do
  requireType ty IntConcrete
  pure $ ([], IntLit i)

checkExpr gamma (BoolLit b) ty = do
  requireType ty BoolConcrete
  pure $ ([], BoolLit b)

checkExpr gamma e@(And {}) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Or {}) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Not {}) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Add {}) ty = do
  requireType ty IntConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Sub {}) ty = do
  requireType ty IntConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Mul {}) ty = do
  requireType ty IntConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Equal x y) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Le x y) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Lt x y) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr gamma e
  pure (loweredParams ty', e')

checkExpr gamma e@(Instantiate inLayoutNames outLayoutName f args) ty = do
  (ty', e') <- inferExpr gamma e
  requireType ty $ forgetParams ty'
  pure (loweredParams ty', e')

checkExpr gamma e@(Lower {}) ty = do
  (ty', e') <- inferExpr gamma e
  requireType ty $ forgetParams ty'
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

inferExpr :: TcEnv -> Parsed ExprX String -> TypeCheck (LoweredType, Elaborated ExprX String)
inferExpr gamma (Var () v) =
  case lookup v gamma of
    Nothing -> error $ "inferExpr: variable not found in TcEnv: " ++ v
    Just concTy -> do
      -- typeMatchesLowered ty lowered
      -- requireType ty (loweredType lowered)

      let lowered = withParams [v] concTy
      pure $ (lowered, Var lowered v)
inferExpr gamma (IntLit i) = do
  pure (IntConcrete, IntLit i)

inferExpr gamma (BoolLit b) = do
  pure (BoolConcrete, BoolLit b)

inferExpr gamma (And x y) = do
  ([], x') <- checkExpr gamma x BoolConcrete
  ([], y') <- checkExpr gamma y BoolConcrete
  pure $ (BoolConcrete, And x' y')

inferExpr gamma (Or x y) = do
  ([], x') <- checkExpr gamma x BoolConcrete
  ([], y') <- checkExpr gamma y BoolConcrete
  pure $ (BoolConcrete, Or x' y')

inferExpr gamma (Not x) = do
  ([], x') <- checkExpr gamma x BoolConcrete
  pure $ (BoolConcrete, Not x')

inferExpr gamma (Add x y) = do
  ([], x') <- checkExpr gamma x IntConcrete
  ([], y') <- checkExpr gamma y IntConcrete
  pure $ (IntConcrete, Add x' y')

inferExpr gamma (Sub x y) = do
  ([], x') <- checkExpr gamma x IntConcrete
  ([], y') <- checkExpr gamma y IntConcrete
  pure $ (IntConcrete, Sub x' y')

inferExpr gamma (Mul x y) = do
  ([], x') <- checkExpr gamma x IntConcrete
  ([], y') <- checkExpr gamma y IntConcrete
  pure $ (IntConcrete, Mul x' y')

inferExpr gamma (Equal x y) = do
  ([], x') <- checkExpr gamma x IntConcrete
  ([], y') <- checkExpr gamma y IntConcrete
  pure $ (BoolConcrete, Equal x' y')

inferExpr gamma (Le x y) = do
  ([], x') <- checkExpr gamma x IntConcrete
  ([], y') <- checkExpr gamma y IntConcrete
  pure $ (BoolConcrete, Le x' y')

inferExpr gamma (Lt x y) = do
  ([], x') <- checkExpr gamma x IntConcrete
  ([], y') <- checkExpr gamma y IntConcrete
  pure $ (BoolConcrete, Lt x' y')

inferExpr gamma e0@(Instantiate inLayoutNames outLayoutName f args) = do
  if length args /= length inLayoutNames
    then typeError $ "Wrong number of arguments. Expected " ++ show (length inLayoutNames) ++ ", found " ++ show (length args) ++ " in: " ++ show e0
    else pure ()

  args' <-
    sequenceA $
      zipWith
        (checkExpr gamma)
        args
        (map LayoutConcrete inLayoutNames)

  def <- lookupDefM f

  outLayout <- lookupLayoutM $ baseLayoutName outLayoutName
  let outLayoutParams = layoutSuSLikParams outLayout

  -- loweredTy <- genLoweredType outLayout

  outVars <- newOutVars outLayout

  let loweredTy = MkLowered outVars outLayoutName

  pure $ (loweredTy
         ,
          Apply
            (getPredName f (map genLayoutName inLayoutNames) (genLayoutName outLayoutName)) -- Name
            loweredTy -- Output layout
            (zipWith MkLowered (map fst args') inLayoutNames)
            (map snd args') -- fun-SuSLik args
         )

inferExpr gamma (Lower layoutName (Var () v)) = do
  -- requireType ty $ LayoutConcrete layoutName
  inferExpr gamma (Var () v)
    -- TODO: Does this need a copy (so, a different out var)?

inferExpr gamma (Lower layoutName (ConstrApply ty' cName args)) = do
    -- TODO: Check that the ADT matches the layout

  layout <- lookupLayoutM (baseLayoutName layoutName)

  -- ty'' <- genLoweredType layout

  outVars <- newOutVars layout
  let ty'' = MkLowered outVars layoutName

  argsWithTys <- traverse (inferWith gamma layout) args

  pure $ (ty'', ConstrApply ty'' cName (map snd argsWithTys))

inferExpr gamma e@(Lower {}) =
  typeError $ "'lower' expression with incorrect form. Should be of the form 'lower v' or 'lower (C ...)'. Found: " ++ show e

inferExpr gamma e@(ConstrApply {}) =
  typeError $ "Un-lowered constructor application: " ++ show e

inferExpr gamma e@(Apply {}) =
  typeError $ "Un-instantiated function application: " ++ show e

