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
import           Data.Maybe

import           Control.Arrow (first, second, (&&&), (***))

import           GHC.Stack

import Debug.Trace

findMaxIndex :: [Heaplet SuSLikName] -> SuSLikName -> Int
findMaxIndex heaplets name = go 0 heaplets + 1
  where
    go curr [] = curr
    go curr (PointsToS (Here _) _ : rest) = go curr rest
    go curr (PointsToS (x :+ i) _ : rest)
      | x == name = go (max curr i) rest
      | otherwise = go curr rest
    go curr (HeapletApplyS _ _ : rest) = go curr rest
    go curr (BlockS x i : rest) -- NOTE: This overrides everything else for now
      | x == name = i
      | otherwise = go curr rest

genBlock :: [Heaplet SuSLikName] -> SuSLikName -> [Heaplet SuSLikName]
genBlock heaplets name =
  let ix = (findMaxIndex heaplets name)
  in
    if ix > 1
      then [BlockS name ix]
      else []

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

genPatternHeaplets :: HasCallStack => Layout -> Pattern FsName -> Assertion' FsName
genPatternHeaplets layout (MkPattern cName args) =
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
getCond :: Layout -> [SuSLikName] -> (Pattern FsName, Expr FsName) -> SuSLikExpr FsName
getCond layout suslikParams (pat, cond) =
  mkAndS (genPatCond suslikParams (genPatternHeaplets layout pat))
         (toSuSLikExpr_unsafe cond)

genBranch :: [Layout] -> Layout -> Layout -> [SuSLikName] -> ((Pattern FsName, Expr FsName), Expr FsName) -> SuSLikBranch
genBranch defs inputLayout outputLayout suslikParams (guardedPat@(pat, _), rhs) =
  let patHeaplets = toHeaplets' $ removeAppsLayout (genPatternHeaplets inputLayout pat)
      lowered = lower' defs outputLayout [retName] rhs
      rhs0 = patHeaplets <> toHeaplets' lowered
  in
  MkSuSLikBranch
  { suslikBranchCond = getCond inputLayout suslikParams guardedPat
  , suslikBranchRhs = concatMap (genBlock rhs0) (retName : suslikParams) <> rhs0
  }

genDefPreds :: [Layout] -> Layout -> Layout -> Def -> [InductivePred]
genDefPreds defs inputLayout outputLayout fnDef =
  let suslikParams = layoutSuSLikParams inputLayout

      branches = getBranches fnDef

      -- suslikBranches =
      --   map (\branch -> genBranch defs layout fnDef (defBranchBody branch) (genCond defBranch) )

        -- map (\(name, branch) -> genBaseBranch defs layout (defName fnDef) (defBranchPattern branch) (layoutSuSLikParams layout) name branch) branchesWithNames

      basePred =
        MkInductivePred
        { inductivePredName = defName fnDef
        , inductivePredParams = retParam : map (locParam . nameToString) suslikParams
        , inductivePredBranches = map (genBranch defs inputLayout outputLayout suslikParams) branches
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
  { suslikSigName = defName def <> "_proc"
  , suslikSigParams = retParam : map (locParam . nameToString) suslikParams
  , suslikSigPre = [PointsToS (Here (ppr retName)) (IntS 0), HeapletApplyS (layoutName layout) suslikParamsS]
  , suslikSigPost = [PointsToS (Here (ppr retName)) (VarS retString), HeapletApplyS (defName def) (VarS retString : suslikParamsS)]
  }

genLayoutPred :: Layout -> InductivePred
genLayoutPred layout =
  MkInductivePred
  { inductivePredName = layoutName layout
  , inductivePredParams = map (locParam . ppr) $ layoutSuSLikParams layout
  , inductivePredBranches = map (layoutPredBranch layout . fst) (layoutBranches layout)
  }

layoutPredBranch :: Layout -> Pattern FsName -> SuSLikBranch
layoutPredBranch layout pat =
  let suslikParams = layoutSuSLikParams layout
      rhs = toHeaplets' $ removeSuSLikArgs $ genPatternHeaplets layout pat
  in
  MkSuSLikBranch
  { suslikBranchCond = genPatCond suslikParams
                                  (genPatternHeaplets layout pat)
  , suslikBranchRhs = concatMap (genBlock rhs) suslikParams <> rhs
  }

removeSuSLikArgs :: Assertion' FsName -> Assertion' FsName
removeSuSLikArgs = go
  where
    go Emp = Emp
    go (PointsTo x y rest) = PointsTo x y (go rest)
    go (HeapletApply layoutName _ fsArg rest) = HeapletApply layoutName [] fsArg (go rest)

-- restrictParams :: [SuSLikName] -> [Heaplet SuSLikName] -> [Heaplet SuSLikName]
-- restrictParams params = map go
--   where
--     go orig@(PointsToS {}) = orig
--     go orig@(BlockS {}) = orig
--     go (HeapletApplyS f args) = HeapletApplyS f (mapMaybe goExpr args)
--
--     goExpr (VarS v)
--       | v `elem` params = Just $ VarS v

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

treeLayout :: Layout
treeLayout =
  mkLayout
    "treeLayout"
    "Tree"
    [suslikName "x"]
    [ (MkPattern "Leaf" [], Emp)
    , (MkPattern "Node" [fsName "payload", fsName "left", fsName "right"]
        ,(PointsTo (Here $ Var $ suslikName "x") (Var (fsName "payload"))
         (PointsTo (Var (suslikName "x") :+ 1) (Var (suslikName "left"))
         (PointsTo (Var (suslikName "x") :+ 2) (Var (suslikName "right"))
         (HeapletApply "treeLayout" [Var $ freeVar "leftX"] (Var (suslikName "left"))
         (HeapletApply "treeLayout" [Var $ freeVar "rightX"] (Var (suslikName "right")) Emp))))))
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

evenTest :: Def
evenTest =
  MkDef
  { defName = "even"
  , defType = Syntax.Simple.Expr.IntType -- Placeholder
  , defBranches =
      [MkDefBranch (MkPattern "Nil" [])
          [MkGuardedExpr (BoolLit True)
            (ConstrApply "Nil" [])
          ]
      ,MkDefBranch (MkPattern "Cons" [MkName "head", MkName "tail"])
          [MkGuardedExpr (BoolLit True)
            (Apply "odd" (Var (MkName "tail")))
          ]
      ]
  }

oddTest :: Def
oddTest =
  MkDef
  { defName = "odd"
  , defType = Syntax.Simple.Expr.IntType -- Placeholder
  , defBranches =
      [MkDefBranch (MkPattern "Nil" [])
          [MkGuardedExpr (BoolLit True)
            (ConstrApply "Nil" [])
          ]
      ,MkDefBranch (MkPattern "Cons" [MkName "head", MkName "tail"])
          [MkGuardedExpr (BoolLit True)
            (ConstrApply "Cons" [Var (MkName "head")
                                ,Apply "even" (Var (MkName "tail"))
                                ])
          ]
      ]
  }

leftListTest :: Def
leftListTest =
  MkDef
  { defName = "leftList"
  , defType = Syntax.Simple.Expr.IntType -- Placeholder
  , defBranches =
      [MkDefBranch (MkPattern "Leaf" [])
          [MkGuardedExpr (BoolLit True)
            (ConstrApply "Nil" [])
          ]
      ,MkDefBranch (MkPattern "Node" [MkName "a", MkName "left", MkName "right"])
          [MkGuardedExpr (BoolLit True)
            (ConstrApply "Cons" [Var (MkName "a")
                                ,Apply "leftList" (Var (MkName "left"))
                                ])
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

