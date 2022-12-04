{-# LANGUAGE LiberalTypeSynonyms #-}

module Syntax.Simple.GenerateNames
  (generateNames)
  where

import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik

import           Syntax.Name
import           Syntax.Ppr

import           Syntax.FreshGen

import           Control.Applicative

import Debug.Trace

-- genParamName :: FreshGen String
-- genParamName = 

type NameEnv =
  [( FsName       -- Pattern variable
   , [SuSLikName] -- SuSLik representation (these are layout parameters if it has a layout type rather than a base type)
   )]

parameterSuffix :: String
parameterSuffix = "_p"

generateNames :: [Layout] -> ElaboratedDef -> NamedDef
generateNames layouts def =
  def
  { defBranches = map branchTranslate (defBranches def)
  , defType = (newArgTypes, newResultType)
  }
  where
    (argTypes, resultType) = defType def
    newArgTypes = 
      snd $
      runFreshGen $
      mapM (transformParamType parameterSuffix) argTypes

    newResultType =
      snd $
      runFreshGen $
      transformParamType "_r" resultType

    branchTranslate :: ElaboratedDefBranch -> NamedDefBranch
    branchTranslate branch =
      let
        newPats :: [Pattern' ParamTypeP]
        newPats =
          zipWith patternSet newArgTypes $ defBranchPatterns branch

        gamma :: NameEnv
        gamma =
          concat $
          snd $
          runFreshGen $
          sequenceA $
          zipWith generatePatternNames argTypes (defBranchPatterns branch)

        goExpr :: ElaboratedExpr String -> Named ExprX String
        goExpr =
          -- trace ("new results = " ++ show (loweredParams newResultType)) $
          setOutput (loweredParams newResultType) .
          setVarParams layouts gamma (loweredParams newResultType)

        guardedTranslate :: NameEnv -> Elaborated GuardedExpr -> Named GuardedExpr
        guardedTranslate pats (MkGuardedExpr cond body) =
          MkGuardedExpr
            (goExpr cond)
            (goExpr body)

      in
      branch
      { defBranchPatterns = newPats
      , defBranchGuardeds = map (guardedTranslate gamma) (defBranchGuardeds branch)
      }

    transformPattern :: ParamType -> Pattern -> FreshGen (Pattern' ParamTypeP)
    transformPattern ty pat = do
      ty' <- transformParamType parameterSuffix ty
      pure $ fmap (const ty') pat



    -- | Transform by freshening layout parameters
    transformParamType :: String -> ParamType -> FreshGen ParamTypeP
    transformParamType _ (PtrParam x y) = pure $ PtrParam x y
    transformParamType _ (IntParam x) = pure $ IntParam x
    transformParamType _ (BoolParam x) = pure $ BoolParam x
    transformParamType suffix (LayoutParam name) = do
      let layout = lookupLayout layouts (baseLayoutName name)

      params <- freshSuSLikParams suffix (layoutSuSLikParams layout)

      pure $ LayoutParam (MkParametrizedLayoutName (map Here params) name)

    generatePatternNames :: ParamType -> Pattern -> FreshGen [(FsName, [SuSLikName])]
    generatePatternNames (LayoutParam name) pat =
      let layout = lookupLayout layouts (baseLayoutName name)
      in
      generatePatternNames_Layout layout pat
    generatePatternNames _ (PatternVar () v) = pure [(v, [v])]

    generatePatternNames_Layout :: Layout -> Pattern -> FreshGen [(FsName, [SuSLikName])]
    generatePatternNames_Layout layout (PatternVar () v) = pure [(v, [v])]
    generatePatternNames_Layout layout (MkPattern () cName patVars) = do
      let (_, asn) = lookupLayoutBranch layout cName
      -- newPatVars <- freshSuSLikParams "p_" patVars
      let newPatVars = patVars
      pure $ zip patVars (map (lookupParams asn) newPatVars)

    -- | If there is an application heaplet associated with the name, use
    -- those names. If not, just use the given name
    lookupParams :: Assertion FsName -> FsName -> [SuSLikName]
    lookupParams asn name = go asn
      where
        go Emp = [name]
        go (PointsTo _ _ _ rest) = go rest
        go (HeapletApply lName suslikParams [Var () v] rest)
          | v == name = map toVar suslikParams
        go (HeapletApply _ _ _ rest) = go rest
        go (Block _ _ rest) = go rest
        go (TempLoc _ rest) = go rest
        go (IsNull _) = [name]
        go (Copy _ _ _) = [name]
        go (AssertEqual _ _ rest) = go rest


    toVar :: SuSLikExpr a -> a
    toVar (VarS v) = v

freshenLayoutParams :: Layout -> FreshGen [SuSLikName]
freshenLayoutParams layout = do
  newParams <- freshSuSLikParams parameterSuffix (layoutSuSLikParams layout)
  pure newParams 

freshSuSLikParams :: String -> [SuSLikName] -> FreshGen [SuSLikName]
freshSuSLikParams suffix = mapM go
  where
    go n = getFreshWith (n <> "__" <> suffix)

setVarParams :: [Layout] -> NameEnv -> [SuSLikName] -> ElaboratedExpr FsName -> Named ExprX SuSLikName
setVarParams layouts env outs0 = snd . runFreshGen . go outs0
  where
    go :: [SuSLikName] -> ElaboratedExpr FsName -> FreshGen (Named ExprX SuSLikName)
    go outs (Var p x) =
      case lookup x env of
        Nothing -> error $ "Cannot find " ++ show x ++ " in " ++ show env
        Just suslikParams ->
          -- trace ("setting name " ++ show x ++ " --> " ++ show suslikParams) $
          pure $ Var (mkParamTypeP suslikParams p) x

    go outs (IntLit i) = pure $ IntLit i
    go outs (BoolLit b) = pure $ BoolLit b
    go outs (And x y) = liftA2 And (go' x) (go' y)
    go outs (Or x y) = liftA2 Or (go' x) (go' y)
    go outs (Not x) = fmap Not (go' x)
    go outs (Add x y) = liftA2 Add (go' x) (go' y)
    go outs (Sub x y) = liftA2 Sub (go' x) (go' y)
    go outs (Mul x y) = liftA2 Mul (go' x) (go' y)
    go outs (Equal x y) = liftA2 Equal (go' x) (go' y)
    go outs (Le x y) = liftA2 Le (go' x) (go' y)
    go outs (Lt x y) = liftA2 Lt (go' x) (go' y)

    go outs (Apply fName outTy argTys fsArgs) = do
      let outTy' = mkParamTypeP outs outTy

      (argNames, argTys') <- fmap unzip $ mapM toParamTypeP argTys

      args' <- sequenceA $ zipWith go argNames fsArgs

      pure $ Apply fName outTy' argTys' args'

    go outs (ConstrApply ty cName args) = do
      (_, ty') <- toParamTypeP ty
      ConstrApply ty' cName <$> mapM go' args


    go outs (Deref ty e) = undefined
    go outs (Addr ty e) = undefined
    go outs (LetIn ty x lhs body) = undefined
    go outs (IfThenElse ty c t f) = undefined

    go' e = do
      outName <- getFreshWith "__i__"
      go [outName] e

    toParamTypeP :: ParamType -> FreshGen ([SuSLikName], ParamTypeP)
    toParamTypeP p = do
      outNames <- freshNamesForType p
      pure (outNames, mkParamTypeP outNames p)

    freshNamesForType :: ParamType -> FreshGen [SuSLikName]
    freshNamesForType (LayoutParam layoutName) = 
      let layout = lookupLayout layouts (baseLayoutName layoutName)
      in
      freshenLayoutParams layout

    freshNamesForType _ = fmap (:[]) $ getFreshWith parameterSuffix

setOutput :: [SuSLikName] -> Named ExprX String -> Named ExprX String
setOutput newOuts e0 = go e0
  where
    go (Var ty v) = Var (overwriteLayoutParams newOuts ty) v
    go (IntLit i) = e0
    go (BoolLit b) = e0
    go (And x y) = e0
    go (Or x y) = e0
    go (Not x) = e0
    go (Add x y) = e0
    go (Sub x y) = e0
    go (Mul x y) = e0
    go (Equal x y) = e0
    go (Le x y) = e0
    go (Lt x y) = e0

    go (Apply fName outTy argTys fsArgs) =
      Apply
        fName
        (overwriteLayoutParams newOuts outTy)
        argTys
        fsArgs

    go (ConstrApply ty cName args) =
      ConstrApply
        (overwriteLayoutParams newOuts ty)
        cName
        args

    go (Deref ty e) =
      Deref (overwriteLayoutParams newOuts ty) e
    go (Addr ty e) =
      Addr (overwriteLayoutParams newOuts ty) e
    go (LetIn ty x lhs body) =
      LetIn (overwriteLayoutParams newOuts ty) x lhs body
    go (IfThenElse ty c t f) =
      IfThenElse (overwriteLayoutParams newOuts ty) c t f

