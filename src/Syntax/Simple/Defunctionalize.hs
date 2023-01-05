{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TupleSections #-}

module Syntax.Simple.Defunctionalize (defunctionalize, baseFnName) where

import           Control.Applicative
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.List
import           Data.Void
import           Data.Maybe

import           Syntax.FreshGen
import           Syntax.Simple.Heaplet
import           Syntax.Simple.Parse
import           Syntax.Ppr

import Debug.Trace


defunctionalize :: [ParsedDef] -> [Layout] -> ParsedDef -> (ParsedDef, [(Directive, ParsedDef)])
defunctionalize globals layouts origDef =
  let (newDef, generated) = runDefun $ runWriterT (defGo origDef)
      generatedDefs = map snd generated
      subst = zip (map (baseFnName . defName) generatedDefs) (map defName generatedDefs)
  in
    (substFnApplyName subst newDef, generated)
  where
    defGo :: ParsedDef -> WriterT [(Directive, ParsedDef)] Defun ParsedDef
    defGo def = do
      newBranches <- traverse branchGo (defBranches def)
      pure def
        { defBranches = newBranches
        , defType = removeFnsFromType (defType def)
        }
      where
        branchGo branch = do
          newGuardeds <- traverse goGuarded (defBranchGuardeds branch)
          pure branch { defBranchGuardeds = newGuardeds }

        goGuarded (MkGuardedExpr cond body) =
          MkGuardedExpr <$> go cond <*> go body

        go :: ParsedExpr String -> WriterT [(Directive, ParsedDef)] Defun (ParsedExpr String)
        go (Lower ty x) = go x
        go (Instantiate inLayouts outLayout fName args) =
          if fName /= defName def && FnParam `elem` inLayouts && any ((== fName) . defName) globals
            then do
              let appDef = lookupDef globals fName
              let ixs = getFnParamPositions appDef
              newDef <- fmap (removeFnPatterns ixs) <$> lift (defunApplication globals fName args)

              let newName = maybe fName defName newDef
                  directive = GenerateDef newName (filter (/= FnParam) inLayouts) outLayout

              tell $ maybeToList (fmap (directive ,) (fmap (updateRecCalls ixs) newDef))

              ys <- traverse go args
              pure $ Instantiate (removeIndices ixs inLayouts) outLayout fName (removeIndices ixs args)
            else
              Instantiate inLayouts outLayout fName <$> traverse go args
        go (Var ty v) = pure $ Var ty v
        go (IntLit i) = pure $ IntLit i
        go (BoolLit b) = pure $ BoolLit b
        go (Add x y) = liftA2 Add (go x) (go y)
        go (Sub x y) = liftA2 Sub (go x) (go y)
        go (Mul x y) = liftA2 Mul (go x) (go y)
        go (And x y) = liftA2 And (go x) (go y)
        go (Or x y) = liftA2 Or (go x) (go y)
        go (Not x) = Not <$> go x
        go (Equal x y) = liftA2 Equal (go x) (go y)
        go (Le x y) = liftA2 Le (go x) (go y)
        go (Lt x y) = liftA2 Lt (go x) (go y)
        go (Deref ty x) = Deref ty <$> go x
        go (Addr ty x) = Addr ty <$> go x
        go (LetIn ty v rhs body) =
          liftA2 (LetIn ty v) (go rhs) (go body)
        go (IfThenElse ty c t f) =
          liftA3 (IfThenElse ty) (go c) (go t) (go f)
        go (Apply fName outLayout inLayouts args) =
          -- Apply fName outLayout inLayouts <$> traverse go args
          -- xs <- fmap maybeToList (lift (defunApplication globals fName args))
          -- ys <- traverse go args
          let ixs = getFnParamPositions def
          in
          pure $ Apply fName outLayout (removeIndices ixs inLayouts) (removeIndices ixs args)
        go (ConstrApply ty cName args) =
          ConstrApply ty cName <$> traverse go args

defunApplication :: [ParsedDef] -> String -> [ParsedExpr String] -> Defun (Maybe ParsedDef)
defunApplication globals fName args =
    let def = lookupDef globals fName
    in
    case getFnArgs def args of
      [] -> pure Nothing
      fnArgs -> do
        newName <- defunctionalizedName (defName def) fnArgs
        let subst = zip (getFnParamPositions def) fnArgs
        pure $ Just $ substFnApply subst def
          { defName = newName
          , defType = removeFnsFromType (defType def)
          }

getFnParamPositions :: ParsedDef -> [Int]
getFnParamPositions def = mapMaybe go $ zip (getArgTypes (defType def)) [0..]
  where
    go :: (Type, Int) -> Maybe Int
    go (FnType {}, i) = Just i
    go _ = Nothing

getFnArgs :: ParsedDef -> [ParsedExpr String] -> [String]
getFnArgs def = mapMaybe go . zip (getArgTypes (defType def))
  where
    go :: (Type, ParsedExpr String) -> Maybe String
    go (FnType {}, Var () name) = Just name
    go (FnType {}, e) = error $ "getFnArgs: Function argument must be a function name, got " ++ show e
    go _ = Nothing

getNonFnArgs :: ParsedDef -> [ParsedExpr String] -> [ParsedExpr String]
getNonFnArgs def = mapMaybe go . zip (getArgTypes (defType def))
  where
    go :: (Type, ParsedExpr String) -> Maybe (ParsedExpr String)
    go (FnType {}, _) = Nothing
    go (_, e) = Just e

removeFnsFromType :: Type -> Type
removeFnsFromType (FnType (FnType {}) cod) = removeFnsFromType cod
removeFnsFromType (FnType dom cod) = FnType dom (removeFnsFromType cod)
removeFnsFromType t = t

removeIndices :: [Int] -> [a] -> [a]
removeIndices = go 0
  where
    go _ _ [] = []
    go here ixs (x:xs)
      | here `elem` ixs = go (here+1) ixs xs
      | otherwise       = x : go (here+1) ixs xs

newtype Defun a = MkDefun (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

runDefun :: Defun a -> a
runDefun (MkDefun m) = evalState m 0

-- NOTE: This will need to be changed if we allow function arguments that
-- are not just variables
defunctionalizedName :: String -> [String] -> Defun String
defunctionalizedName fnName fnArgs = do
  uniq <- get
  modify succ
  pure (fnName ++ "__df_" ++ intercalate "_" fnArgs ++ show uniq)

removeFnPatterns :: [Int] -> ParsedDef -> ParsedDef
removeFnPatterns ixs def =
  def
    { defBranches = map branchGo (defBranches def)
    }
  where
    branchGo branch =
      branch
        { defBranchPatterns =
            removeIndices ixs (defBranchPatterns branch)
        }

updateRecCalls :: [Int] -> ParsedDef -> ParsedDef
updateRecCalls ixs def =
  def
    { defBranches = map branchGo (defBranches def)
    }
  where

    branchGo branch =
      branch
        { defBranchGuardeds = map goGuarded (defBranchGuardeds branch)
        }
      where
        equalsParamAtPos :: [Pattern] -> Int -> String -> Bool
        equalsParamAtPos [] pos name = False
        equalsParamAtPos (PatternVar _ patName : _) 0 name = name == patName
        equalsParamAtPos (MkPattern {} : _) 0 name = error "substFnApply: Expected pattern variable for function parameter"
        equalsParamAtPos (_ : rest) n name = equalsParamAtPos rest (n-1) name


        goGuarded (MkGuardedExpr cond body) =
          MkGuardedExpr (go cond) (go body)

        go :: ParsedExpr String -> ParsedExpr String
        go (Lower ty x) = go x
        go (Instantiate inLayouts outLayout fName args) =
          if baseFnName fName == baseFnName (defName def)
            then
              Instantiate (removeIndices ixs inLayouts) outLayout fName (map go (removeIndices ixs args))
            else Instantiate inLayouts outLayout fName (map go args)
        go (Var ty v) = Var ty v
        go (IntLit i) = IntLit i
        go (BoolLit b) = BoolLit b
        go (Add x y) = Add (go x) (go y)
        go (Sub x y) = Sub (go x) (go y)
        go (Mul x y) = Mul (go x) (go y)
        go (And x y) = And (go x) (go y)
        go (Or x y) = Or (go x) (go y)
        go (Not x) = Not (go x)
        go (Equal x y) = Equal (go x) (go y)
        go (Le x y) = Le (go x) (go y)
        go (Lt x y) = Lt (go x) (go y)
        go (Deref ty x) = Deref ty (go x)
        go (Addr ty x) = Addr ty (go x)
        go (LetIn ty v rhs body) =
          LetIn ty v (go rhs) (go body)
        go (IfThenElse ty c t f) =
          IfThenElse ty (go c) (go t) (go f)
        go (Apply fName outLayout inLayouts args) =
          if baseFnName fName == baseFnName (defName def)
            then
              Apply fName outLayout (removeIndices ixs inLayouts) (map go (removeIndices ixs args))
            else
              Apply fName outLayout inLayouts (map go args)
        go (ConstrApply ty cName args) =
          ConstrApply ty cName (map go args)

substFnApply :: [(Int, String)] -> ParsedDef -> ParsedDef
substFnApply subst def = foldr substFnApply1 def subst

substFnApply1 :: (Int, String) -> ParsedDef -> ParsedDef
substFnApply1 (paramPosition, newName) def =
  def
    { defBranches = map branchGo (defBranches def)
    }
  where

    branchGo branch =
      branch
        { defBranchGuardeds = map goGuarded (defBranchGuardeds branch)
        }
      where
        equalsParamAtPos :: [Pattern] -> Int -> String -> Bool
        equalsParamAtPos [] pos name = False
        equalsParamAtPos (PatternVar _ patName : _) 0 name = name == patName
        equalsParamAtPos (MkPattern {} : _) 0 name = error "substFnApply: Expected pattern variable for function parameter"
        equalsParamAtPos (_ : rest) n name = equalsParamAtPos rest (n-1) name


        goGuarded (MkGuardedExpr cond body) =
          MkGuardedExpr (go cond) (go body)

        go :: ParsedExpr String -> ParsedExpr String
        go (Lower ty x) = go x
        go (Instantiate inLayouts outLayout fName0 args) =
          let fName =
                if equalsParamAtPos (defBranchPatterns branch) paramPosition fName0
                  then newName
                  else fName0
           in Instantiate inLayouts outLayout fName (map go args)
        go (Var ty v) = Var ty v
        go (IntLit i) = IntLit i
        go (BoolLit b) = BoolLit b
        go (Add x y) = Add (go x) (go y)
        go (Sub x y) = Sub (go x) (go y)
        go (Mul x y) = Mul (go x) (go y)
        go (And x y) = And (go x) (go y)
        go (Or x y) = Or (go x) (go y)
        go (Not x) = Not (go x)
        go (Equal x y) = Equal (go x) (go y)
        go (Le x y) = Le (go x) (go y)
        go (Lt x y) = Lt (go x) (go y)
        go (Deref ty x) = Deref ty (go x)
        go (Addr ty x) = Addr ty (go x)
        go (LetIn ty v rhs body) =
          LetIn ty v (go rhs) (go body)
        go (IfThenElse ty c t f) =
          IfThenElse ty (go c) (go t) (go f)
        go (Apply fName0 outLayout inLayouts0 args0) =
          let 
              fName =
                if equalsParamAtPos (defBranchPatterns branch) paramPosition fName0
                  then newName
                  else fName0
           in
             Apply fName outLayout inLayouts0 (map go args0)
        go (ConstrApply ty cName args) =
          ConstrApply ty cName (map go args)



substFnApplyName :: [(String, String)] -> ParsedDef -> ParsedDef
substFnApplyName subst def = foldr substFnApplyName1 def subst

substFnApplyName1 :: (String, String) -> ParsedDef -> ParsedDef
substFnApplyName1 (oldName, newName) def =
  def
    { defBranches = map branchGo (defBranches def)
    }
  where

    branchGo branch =
      branch
        { defBranchGuardeds = map goGuarded (defBranchGuardeds branch)
        }
      where
        equalsParamAtPos :: [Pattern] -> Int -> String -> Bool
        equalsParamAtPos [] pos name = False
        equalsParamAtPos (PatternVar _ patName : _) 0 name = name == patName
        equalsParamAtPos (MkPattern {} : _) 0 name = error "substFnApply: Expected pattern variable for function parameter"
        equalsParamAtPos (_ : rest) n name = equalsParamAtPos rest (n-1) name


        goGuarded (MkGuardedExpr cond body) =
          MkGuardedExpr (go cond) (go body)

        go :: ParsedExpr String -> ParsedExpr String
        go (Lower ty x) = go x
        go (Instantiate inLayouts outLayout fName0 args) =
          let fName =
                if fName0 == oldName
                  then newName
                  else fName0
           in Instantiate inLayouts outLayout fName (map go args)
        go (Var ty v) = Var ty v
        go (IntLit i) = IntLit i
        go (BoolLit b) = BoolLit b
        go (Add x y) = Add (go x) (go y)
        go (Sub x y) = Sub (go x) (go y)
        go (Mul x y) = Mul (go x) (go y)
        go (And x y) = And (go x) (go y)
        go (Or x y) = Or (go x) (go y)
        go (Not x) = Not (go x)
        go (Equal x y) = Equal (go x) (go y)
        go (Le x y) = Le (go x) (go y)
        go (Lt x y) = Lt (go x) (go y)
        go (Deref ty x) = Deref ty (go x)
        go (Addr ty x) = Addr ty (go x)
        go (LetIn ty v rhs body) =
          LetIn ty v (go rhs) (go body)
        go (IfThenElse ty c t f) =
          IfThenElse ty (go c) (go t) (go f)
        go (Apply fName0 outLayout inLayouts0 args0) =
          let fName =
                if fName0 == oldName
                  then newName
                  else fName0
           in
             Apply fName outLayout inLayouts0 (map go args0)
        go (ConstrApply ty cName args) =
          ConstrApply ty cName (map go args)


-- TODO: This is an ugly hack. Use a better way
baseFnName :: String -> String
baseFnName "" = ""
baseFnName str@(c:cs) =
  let marker = "__df_"
  in
  if length str >= length marker && and (zipWith (==) str marker)
    then ""
    else c : baseFnName cs

