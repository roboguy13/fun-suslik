-- {-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module Syntax.Simple.Def
  where

import           Syntax.Simple.Expr
import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik
import           Syntax.Name
import           Syntax.FreshGen
import           Syntax.Ppr

import           Data.Foldable
import qualified Data.Set as Set

import           Data.List

import           Control.Arrow (first, second, (&&&), (***))

import           GHC.Stack

import Debug.Trace

data Def =
  MkDef
  { defName :: String
  , defType :: Type
  , defBranches :: [DefBranch]
  }
  deriving (Show)

data DefBranch =
  MkDefBranch
  { defBranchPattern :: Pattern FsName
  , defBranchGuardeds :: [GuardedExpr]
  }
  deriving (Show)

data GuardedExpr =
  MkGuardedExpr
  { guardedCond :: Expr FsName
  , guardedBody :: Expr FsName
  }
  deriving (Show)

-- toSuSLikExpr :: Expr FsName -> SuSLikExpr SuSLikName
-- toSuSLikExpr (Var v) = VarS v
-- toSuSLikExpr (BoolLit b) = BoolS b
-- toSuSLikExpr (And x y) = AndS (toSuSLikExpr x) (toSuSLikExpr y)
-- toSuSLikExpr (Or x y) = OrS (toSuSLikExpr x) (toSuSLikExpr y)
-- toSuSLikExpr (Not x) = NotS (toSuSLikExpr x)
-- toSuSLikExpr (Add x y) = AndS (toSuSLikExpr x) (toSuSLikExpr y)
-- toSuSLikExpr (Sub x y) = SubS (toSuSLikExpr x) (toSuSLikExpr y)
-- toSuSLikExpr (Mul x y) = MulS (toSuSLikExpr x) (toSuSLikExpr y)
-- toSuSLikExpr (Equal x y) = EqualS (toSuSLikExpr x) (toSuSLikExpr y)
-- toSuSLikExpr (Lt x y) = LtS (toSuSLikExpr x) (toSuSLikExpr y)
-- toSuSLikExpr (Le x y) = LeS (toSuSLikExpr x) (toSuSLikExpr y)

genBranchName :: String -> String -> String
genBranchName str c = str <> "__" <> c

pointsLhsNames :: Ppr a => Assertion' a -> [a]
pointsLhsNames Emp = []
pointsLhsNames (PointsTo x _ rest) = map getVar (toList x) ++ pointsLhsNames rest
pointsLhsNames (HeapletApply _ _ _ rest) = pointsLhsNames rest

genPatCond :: [SuSLikName] -> Assertion' FsName -> SuSLikExpr SuSLikName
genPatCond suslikParams0 asn =
    -- trace ("\nasn names = " ++ show (map ppr (pointsLhsNames asn))) $
    -- trace ("\nsuslikParams = " ++ unwords (map ppr suslikParams0)) $
    foldr mkAndS (BoolS True) $ map go suslikParams0 --(suslikParams0 `intersect` pointsLhsNames asn)
  where
    names = Set.toList . Set.fromList . concat . fmap toList $ toList asn
    go param =
      if param `elem` names
        then NotS (EqualS (VarS param) (IntS 0))
        else EqualS (VarS param) (IntS 0)

nameToString :: Name_ String -> String
nameToString = ppr

connect :: forall a. (HasCallStack, Ppr a) => Expr (Name_ a) -> (SuSLikExpr (Name_ a) -> FreshGen [Heaplet (Name_ a)]) -> FreshGen [Heaplet (Name_ a)]
-- connect (Apply f (Var v)) k = do
--   hs <- k (VarS v)
--   pure $ hs -- ++ [HeapletApplyS f [v]]
connect (Apply f e) k =
    -- trace ("\ne = " ++ ppr e) $
  connect e $ \suslikE -> do
    newVar <- getFresh :: FreshGen (Name_ a)
    heaplets <- k (VarS (newVar))
    pure $ heaplets -- ++ [HeapletApplyS f [newVar]]
connect e k =
  case toSuSLikExpr e of
    Just s -> k s
    Nothing -> error $ "connect: " ++ ppr e

toHeaplets :: (Ppr a) => Assertion' (Name_ a) -> FreshGen [Heaplet (Name_ a)]
toHeaplets Emp = pure []
toHeaplets (PointsTo x y rest) = do
  here <- connect y $ \suslikY -> pure [PointsToS (fmap getVar x) suslikY]
  fmap (here ++) (toHeaplets rest)
toHeaplets (HeapletApply str suslikArgs (Var fsArg) rest) =
    -- trace ("--------- " ++ unwords (map ppr suslikArgs) ++ "; " ++ ppr fsArg) $
  -- fmap (HeapletApplyS str (map getVar suslikArgs ++ [fsArg]) :) (toHeaplets rest)
  fmap (HeapletApplyS str (map toSuSLikExpr_unsafe suslikArgs ++ [VarS fsArg]) :) (toHeaplets rest)
toHeaplets (HeapletApply str suslikArgs fsArg rest) = do
  -- here <- connect fsArg $ \suslikE -> fmap (HeapletApplyS str (map getVar suslikArgs ++ [suslikE]) :) (toHeaplets rest)
  -- traceM $ "\n*********toHeaplets: " ++ show (map ppr suslikArgs) ++ "; " ++ ppr fsArg
  -- let here = [HeapletApplyS str 
  here <- connect fsArg $ \suslikE -> fmap (HeapletApplyS str (map toSuSLikExpr_unsafe suslikArgs ++ [suslikE]) :) (toHeaplets rest)
  fmap (here ++) (toHeaplets rest)
  -- error $ "toHeaplets:  " ++ str ++ "[" ++ intercalate "," (map ppr suslikArgs) ++ "] " ++ ppr fsArg

toHeaplets' :: Ppr a => Assertion' (Name_ a) -> [Heaplet (Name_ a)]
toHeaplets' = snd . runFreshGen . toHeaplets

genPatternHeaplets :: [Layout] -> Layout -> Pattern FsName -> Assertion' FsName
genPatternHeaplets layoutDefs layout (MkPattern cName args) =
    -- TODO: Avoid capture here between the SuSLik parameters and the FS
    -- variables
  applyLayout 0 layout (layoutSuSLikParams layout) cName $ map Var args

branchArgs :: [SuSLikName] -> Pattern FsName -> [SuSLikName]
branchArgs suslikParams (MkPattern _ patParams) = suslikParams ++ patParams

retString :: String
retString = "r"

retParam :: SuSLikParam
retParam = locParam ("_" <> retString)

retName :: SuSLikName
retName = suslikName retString

-- | Collect all the branches with their patterns, guards and bodies
getBranches :: Def -> [((Pattern FsName, Expr FsName), Expr FsName)]
getBranches def =
    map (\(pat, guarded) -> ((pat, guardedCond guarded), guardedBody guarded))
      $ concatMap (\(pat, gs) -> map (pat,) gs)
      $ map (defBranchPattern &&& defBranchGuardeds) (defBranches def)

-- | Turn a guarded pattern match into a SuSLik Boolean expression
getCond :: [Layout] -> Layout -> [SuSLikName] -> (Pattern FsName, Expr FsName) -> SuSLikExpr FsName
getCond defs layout suslikParams (pat, cond) =
  mkAndS (genPatCond suslikParams (genPatternHeaplets defs layout pat))
         (toSuSLikExpr_unsafe cond)

genBranch :: [Layout] -> Layout -> [SuSLikName] -> ((Pattern FsName, Expr FsName), Expr FsName) -> SuSLikBranch
genBranch defs layout suslikParams (guardedPat@(pat, _), rhs) =
  let patHeaplets = toHeaplets' $ removeAppsLayout (genPatternHeaplets defs layout pat)
      lowered = lower' defs layout [retName] rhs
  in
  MkSuSLikBranch
  { suslikBranchCond = getCond defs layout suslikParams guardedPat
  , suslikBranchRhs = patHeaplets <> toHeaplets' lowered
  }

genDefPreds :: [Layout] -> Layout -> Def -> [InductivePred]
genDefPreds defs layout fnDef =
  let suslikParams = layoutSuSLikParams layout

      branches = getBranches fnDef

      -- suslikBranches =
      --   map (\branch -> genBranch defs layout fnDef (defBranchBody branch) (genCond defBranch) )

        -- map (\(name, branch) -> genBaseBranch defs layout (defName fnDef) (defBranchPattern branch) (layoutSuSLikParams layout) name branch) branchesWithNames

      basePred =
        MkInductivePred
        { inductivePredName = defName fnDef
        , inductivePredParams = retParam : map (locParam . nameToString) suslikParams
        , inductivePredBranches = map (genBranch defs layout suslikParams) branches
        }
  in
  [basePred]
  -- basePred : condPreds

genSig :: Layout -> Def -> SuSLikSig
genSig layout def =
  let suslikParams = layoutSuSLikParams layout
      suslikParamsS = map (VarS . ppr) suslikParams
  in
  MkSuSLikSig
  { suslikSigName = defName def
  , suslikSigParams = retParam : map (locParam . nameToString) suslikParams
  , suslikSigPre = [PointsToS (Here retString) (IntS 0), HeapletApplyS (layoutName layout) suslikParamsS]
  , suslikSigPost = [HeapletApplyS (defName def) (VarS retString : suslikParamsS)]
  }


---- Tests ----

sllLayout :: Layout
sllLayout =
  mkLayout
    "sll"
    "List"
    [suslikName "x"]
    [ (MkPattern "Nil" [], Emp)
                       , (MkPattern "Cons" [fsName "head", fsName "tail"]
                         ,(PointsTo (Here $ Var $ suslikName "x") (Var (fsName "head"))
                          (PointsTo (Var (suslikName "x") :+ 1) (Var (suslikName "tail"))
                          (HeapletApply "sll" [Var $ freeVar "nxt"] (Var (fsName "tail")) Emp)))
                         )
                       ]

test1 :: Def
test1 =
  MkDef
  { defName = "filterLt7"
  , defType = Syntax.Simple.Expr.IntType -- Placeholder
  , defBranches =
      [MkDefBranch (MkPattern "Nil" [])
          [MkGuardedExpr (BoolLit True)
            (ConstrApply "Nil" [])
          ]
      ,MkDefBranch (MkPattern "Cons" [MkName "head", MkName "tail"])
          [MkGuardedExpr (Lt (Var (MkName "head")) (IntLit 7))
            (ConstrApply "Cons" [Var (MkName "head")
                                ,Apply "filterLt7" (Var (MkName "tail"))
                                ])
          ,MkGuardedExpr (Not (Lt (Var (MkName "head")) (IntLit 7)))
            (Apply "filterLt7" (Var (MkName "tail")))
          ]
      ]
  }

testApply1 :: Assertion' FsName
testApply1 =
  applyLayout 0 sllLayout [MkName "z"]
    "Cons" [Var $ MkName "a",
      ConstrApply "Cons" [Var $ MkName "b",
        ConstrApply "Cons" [Var $ MkName "c", Var $ MkName "d"]]]

testApply2 :: Assertion' FsName
testApply2 =
  applyLayout 0 sllLayout [MkName "z"]
    "Nil" []

(_, (Right testLower1)) = runFreshGen $ lower [sllLayout] sllLayout [MkName "z"] (ConstrApply "Cons" [Add (Var $ MkName "a") (Var $ MkName "b"), Apply "f" $ Var $ MkName "c"])

