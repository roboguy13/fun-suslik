{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Syntax.Simple.TypeCheck
  where

import           Syntax.Simple.Heaplet
import           Syntax.FreshGen
import           Syntax.Name

import           Data.List
import           Data.Void

-- elaborateExpr :: [Layout] -> [Parsed Def] -> Parsed ExprX a -> Elaborated ExprX a
-- elaborateExpr layouts defs = undefined

type TypeCheck = Either String

type TcEnv = [(String, LoweredType)]

genLoweredType :: Int -> String -> LoweredType
genLoweredType count name =
  MkLoweredType (map go [0..count]) $ LayoutConcrete name
  where
    go n = name <> "__" <> show n

toLoweredType :: [Layout] -> String -> ConcreteType -> (String, LoweredType)
toLoweredType layouts v ty@(LayoutConcrete layoutName) =
    let layout = lookupLayout layouts layoutName
        params = map go $ layoutSuSLikParams layout
    in
    (v, MkLoweredType params ty)
  where
    go n = v <> "__" <> n
toLoweredType _layouts v ty = (v, MkLoweredType [v] ty)

typeMatchesLowered :: Type -> LoweredType -> TypeCheck ()
typeMatchesLowered = go
  where
    go IntType (MkLoweredType [x] IntConcrete) = pure ()
    go BoolType (MkLoweredType [x] BoolConcrete) = pure ()
    go (AdtType name) _ = Left $ "ADT type not lowered: " ++ name
    go (LayoutType name arity)
       (MkLoweredType params (LayoutConcrete name')) =
         if name' /= name
           then Left $ "Expected layout " ++ name ++ " found " ++ name'
           else
             if arity /= length params
               then Left $ "Expected " ++ show arity ++ " arguments to layout " ++ name ++ ", found " ++ show (length params)
               else pure ()
    go (LayoutType name _) lowered =
      Left $ "Expected layout type, found " ++ show lowered
    go ty lowered =
      Left $ "Expected " ++ show ty ++ ", found " ++ show lowered

requireType :: (Eq a, Show a) => a -> a -> TypeCheck ()
requireType expected found =
  if expected == found
    then pure ()
    else Left $ "Expected type " ++ show expected ++ ", found " ++ show found

-- toConcrete :: Type -> TypeCheck ConcreteType
-- toConcrete IntType = pure IntConcrete
-- toConcrete BoolType = pure BoolConcrete
-- toConcrete FnType{} = error "toConcrete: Function type in elaboration stage"
-- toConcrete (AdtType name) = Left $ "Expected concrete type, found ADT " ++ name
-- toConcrete (LayoutType name _) = pure $ LayoutConcrete name

toConcrete :: String -> ConcreteType
toConcrete "Int" = IntConcrete
toConcrete "Bool" = BoolConcrete
toConcrete x = LayoutConcrete x

-- | Get the predicate name for a function with the given layouts
getPredName :: String -> [String] -> String -> String
getPredName fnName argLayouts resultLayout =
  fnName <> "__" <> intercalate "__" (resultLayout : argLayouts)

instAndElaborate :: [Layout] -> [Adt] -> [Parsed Def] -> String -> [String] -> String -> Parsed Def -> Elaborated Def
instAndElaborate layouts adts defs fnName argLayoutNames outLayoutName def =
  elaborateDef layouts adts defs argLayoutNames outLayoutName
    $ instDefCalls argLayoutNames outLayoutName def

instDefCalls :: [String] -> String -> Parsed Def -> Parsed Def
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
instCall :: String -> [String] -> String -> Parsed ExprX String -> Parsed ExprX String
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
    go (Apply f ty args)
      | f == fnName = instantiate (map go args)
      | otherwise = Apply f ty (map go args)
    go (ConstrApply ty cName args) = ConstrApply ty cName (map go args)
    go (Lower layout arg) = Lower layout (go arg)
    go (Instantiate xs ys f args) = Instantiate xs ys f (map go args)

elaborateDef :: [Layout] -> [Adt] -> [Parsed Def] -> [String] -> String -> Parsed Def -> Elaborated Def
elaborateDef layouts adts defs inLayoutNames outLayoutName def =
  def { defBranches = map goBranch (defBranches def) }
  where
    argLayouts = map (lookupLayout layouts) inLayoutNames
    argAdts = map (lookupAdt adts . layoutAdtName) argLayouts

    outLayout = lookupLayout layouts outLayoutName

    goBranch defBranch =
      defBranch { defBranchGuardeds = map goGuarded (defBranchGuardeds defBranch) }
      where
        gamma =
          map (uncurry $ toLoweredType layouts) $
          concat $
          zipWith3 (inferLayoutPatVars layouts)
            argLayouts
            argAdts
              $ defBranchPattern defBranch

        goGuarded (MkGuardedExpr x y) =
          MkGuardedExpr (goExpr x) (goExpr y)

        goExpr e =
          case inferWith layouts defs gamma outLayout e of
            Left err -> error err
            Right (_, e') -> e'

inferLayoutPatVars :: [Layout] -> Layout -> Adt -> Pattern FsName -> [(FsName, ConcreteType)]
inferLayoutPatVars layouts layout adt (PatternVar v) = [(v, LayoutConcrete (layoutName layout))]
inferLayoutPatVars layouts layout adt (MkPattern cName params) =
    let adtFields = adtBranchFields $ findAdtBranch adt cName
    in
    zipWith go params adtFields
  where
    go v IntType = (v, IntConcrete)
    go v BoolType = (v, BoolConcrete)
    go v _ = (v, LayoutConcrete $ findLayoutApp v $ lookupLayoutBranch layout cName)

findLayoutApp :: FsName -> Assertion FsName -> String
findLayoutApp v = go
  where
  go Emp = error "findLayoutApp: Cannot find " ++ show v
  go (PointsTo _ _ _ rest) = go rest
  go (HeapletApply lName params [Var _ v'] rest)
    | v' == v = genLayoutName lName
    | otherwise = go rest
  go (HeapletApply lName params _ rest) = go rest

inferWith :: [Layout] -> [Parsed Def] -> TcEnv -> Layout -> Parsed ExprX String -> TypeCheck (ConcreteType, Elaborated ExprX String)
inferWith layouts defs gamma layout e@(ConstrApply {}) =
  inferExpr layouts defs gamma (Lower (layoutName layout) e)
inferWith layouts defs gamma layout e = inferExpr layouts defs gamma e

checkExpr :: [Layout] -> [Parsed Def] -> TcEnv -> Parsed ExprX String -> ConcreteType -> TypeCheck (Elaborated ExprX String)
checkExpr layouts defs gamma e@(Var () v) ty = do
  (ty', e') <- inferExpr layouts defs gamma e
  requireType ty ty'
  pure e'

checkExpr layouts defs gamma (IntLit i) ty = do
  requireType ty IntConcrete
  pure $ IntLit i

checkExpr layouts defs gamma (BoolLit b) ty = do
  requireType ty BoolConcrete
  pure $ BoolLit b

checkExpr layouts defs gamma e@(And {}) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Or {}) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Not {}) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Add {}) ty = do
  requireType ty IntConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Sub {}) ty = do
  requireType ty IntConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Mul {}) ty = do
  requireType ty IntConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Equal x y) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Le x y) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Lt x y) ty = do
  requireType ty BoolConcrete
  (ty', e') <- inferExpr layouts defs gamma e
  pure e'

checkExpr layouts defs gamma e@(Instantiate inLayoutNames outLayoutName f args) ty = do
  (ty', e') <- inferExpr layouts defs gamma e
  requireType ty ty'
  pure e'

checkExpr layouts defs gamma e@(Lower {}) ty = do
  (ty', e') <- inferExpr layouts defs gamma e
  requireType ty ty'
  pure e'

checkExpr layouts defs gamma e@(ConstrApply {}) ty =
  Left $
    unlines
    [ "Found un-lowered constructor application " ++ show e
    , "Expected concrete type " ++ show ty
    ]

checkExpr layouts defs gamma e@(Apply {}) ty =
  Left $
    unlines
    [ "Found un-instantiated function application " ++ show e
    , "Expected concrete type " ++ show ty
    ]

inferExpr :: [Layout] -> [Parsed Def] -> TcEnv -> Parsed ExprX String -> TypeCheck (ConcreteType, Elaborated ExprX String)
inferExpr layouts defs gamma (Var () v) =
  case lookup v gamma of
    Nothing -> error $ "inferExpr: variable not found in TcEnv: " ++ v
    Just lowered -> do
      -- typeMatchesLowered ty lowered
      -- requireType ty (loweredType lowered)
      pure $ (loweredType lowered, Var lowered v)
inferExpr layouts defs gamma (IntLit i) = do
  pure (IntConcrete, IntLit i)

inferExpr layouts defs gamma (BoolLit b) = do
  pure (BoolConcrete, BoolLit b)

inferExpr layouts defs gamma (And x y) = do
  x' <- checkExpr layouts defs gamma x BoolConcrete
  y' <- checkExpr layouts defs gamma y BoolConcrete
  pure $ (BoolConcrete, And x' y')

inferExpr layouts defs gamma (Or x y) = do
  x' <- checkExpr layouts defs gamma x BoolConcrete
  y' <- checkExpr layouts defs gamma y BoolConcrete
  pure $ (BoolConcrete, Or x' y')

inferExpr layouts defs gamma (Not x) = do
  x' <- checkExpr layouts defs gamma x BoolConcrete
  pure $ (BoolConcrete, Not x')

inferExpr layouts defs gamma (Add x y) = do
  x' <- checkExpr layouts defs gamma x IntConcrete
  y' <- checkExpr layouts defs gamma y IntConcrete
  pure $ (IntConcrete, Add x' y')

inferExpr layouts defs gamma (Sub x y) = do
  x' <- checkExpr layouts defs gamma x IntConcrete
  y' <- checkExpr layouts defs gamma y IntConcrete
  pure $ (IntConcrete, Sub x' y')

inferExpr layouts defs gamma (Mul x y) = do
  x' <- checkExpr layouts defs gamma x IntConcrete
  y' <- checkExpr layouts defs gamma y IntConcrete
  pure $ (IntConcrete, Mul x' y')

inferExpr layouts defs gamma (Equal x y) = do
  x' <- checkExpr layouts defs gamma x IntConcrete
  y' <- checkExpr layouts defs gamma y IntConcrete
  pure $ (BoolConcrete, Equal x' y')

inferExpr layouts defs gamma (Le x y) = do
  x' <- checkExpr layouts defs gamma x IntConcrete
  y' <- checkExpr layouts defs gamma y IntConcrete
  pure $ (BoolConcrete, Le x' y')

inferExpr layouts defs gamma (Lt x y) = do
  x' <- checkExpr layouts defs gamma x IntConcrete
  y' <- checkExpr layouts defs gamma y IntConcrete
  pure $ (BoolConcrete, Lt x' y')

inferExpr layouts defs gamma e0@(Instantiate inLayoutNames outLayoutName f args) = do
  if length args /= length inLayoutNames
    then Left $ "Wrong number of arguments. Expected " ++ show (length inLayoutNames) ++ ", found " ++ show (length args) ++ " in: " ++ show e0
    else Right ()

  args' <-
    sequenceA $
      zipWith
        (checkExpr layouts defs gamma)
        args
        (map toConcrete inLayoutNames)

  let def = lookupDef defs f

      outLayout = lookupLayout layouts outLayoutName
      outLayoutParams = layoutSuSLikParams outLayout

  pure $ (LayoutConcrete outLayoutName
         ,Apply
          (getPredName f inLayoutNames outLayoutName) -- Name
          (genLoweredType (length outLayoutParams) outLayoutName) -- Output layout
          args' -- fun-SuSLik args
         )

inferExpr layouts defs gamma (Lower layoutName (Var () v)) = do
  -- requireType ty $ LayoutConcrete layoutName
  inferExpr layouts defs gamma (Var () v)

inferExpr layouts defs gamma (Lower layoutName (ConstrApply ty' cName args)) = do
    -- TODO: Check that the ADT matches the layout

  let layout = lookupLayout layouts layoutName
      layoutParams = layoutSuSLikParams layout

  let ty'' = genLoweredType (length layoutParams) layoutName

  argsWithTys <- traverse (inferWith layouts defs gamma layout) args

  pure $ (loweredType ty'', ConstrApply ty'' cName (map snd argsWithTys))

inferExpr layouts defs gamma e@(Lower {}) =
  Left $ "'lower' expression with incorrect form. Should be of the form 'lower v' or 'lower (C ...)'. Found: " ++ show e

inferExpr layouts defs gamma e@(ConstrApply {}) =
  Left $ "Un-lowered constructor application: " ++ show e

inferExpr layouts defs gamma e@(Apply {}) =
  Left $ "Un-instantiated function application: " ++ show e

