{-# LANGUAGE OverloadedLists #-}

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

genBranchName :: String -> Int -> String
genBranchName str i = str <> "__" <> show i

genBaseCond :: [SuSLikName] -> Assertion' FsName -> SuSLikExpr SuSLikName
genBaseCond suslikParams0 asn =
    foldr AndS (BoolS True) $ map go suslikParams0
  where
    names = Set.toList . Set.fromList . concat . fmap toList $ toList asn
    go param =
      if param `elem` names
        then NotS (EqualS (VarS param) (IntS 0))
        else EqualS (VarS param) (IntS 0)

nameToString :: Name_ String -> String
nameToString = ppr

toHeaplets :: Ppr a => Assertion' a -> [Heaplet a]
toHeaplets Emp = []
toHeaplets (PointsTo x y rest) = PointsToS (fmap getVar x) (toSuSLikExpr y) : toHeaplets rest
toHeaplets (HeapletApply str suslikArgs _ rest) =
  HeapletApplyS str (map getVar suslikArgs) : toHeaplets rest

genPatternHeaplets :: [Layout] -> Layout -> Pattern FsName -> [Heaplet String]
genPatternHeaplets layoutDefs layout (MkPattern cName args) =
    -- TODO: Avoid capture here between the SuSLik parameters and the FS
    -- variables
  toHeaplets $ fmap (fmap nameToString) $ applyLayout 0 layout (layoutSuSLikParams layout) cName $ map Var args

branchArgs :: [SuSLikName] -> Pattern FsName -> [SuSLikName]
branchArgs suslikParams (MkPattern _ patParams) = suslikParams ++ patParams

replaceRecCall :: String -> String -> Pattern FsName -> Assertion' FsName -> Assertion' FsName
replaceRecCall recName newName pat Emp = Emp
replaceRecCall recName newName pat (PointsTo x y rest) =
  PointsTo x y $ replaceRecCall recName newName pat rest
replaceRecCall recName newName pat (HeapletApply fName suslikParams e rest)
  | fName == recName =
      HeapletApply newName (map Var (branchArgs (map getVar suslikParams) pat)) e
        (replaceRecCall recName newName pat rest)
  | otherwise =
      HeapletApply fName suslikParams e (replaceRecCall recName newName pat rest)

genCondBranch :: [Layout] -> String -> String -> Pattern FsName -> [SuSLikName] -> Expr FsName -> Assertion' FsName -> SuSLikBranch
genCondBranch defs recName newName pat suslikArgs cond asn0 =
  let asn = asn0 --replaceRecCall recName newName pat asn0
  in
  MkSuSLikBranch
  { suslikBranchCond = toSuSLikExpr cond
  , suslikBranchRhs = toHeaplets asn
  }

genCondPred :: [Layout] -> Layout -> String -> String -> DefBranch -> [SuSLikName] -> InductivePred
genCondPred defs layout recName newName (MkDefBranch pat exprs) suslikArgs =
  MkInductivePred
  { inductivePredName = newName
  , inductivePredParams = map (locParam . ppr) $ branchArgs suslikArgs pat
  , inductivePredBranches = map go exprs
  }
  where
    go guarded =
      genCondBranch defs recName newName pat suslikArgs
        (guardedCond guarded)
        (lower' defs layout suslikArgs (guardedBody guarded))

genBaseBranch :: [Layout] -> Layout -> String -> Pattern FsName -> [SuSLikName] -> String -> DefBranch -> SuSLikBranch
genBaseBranch layoutDefs layout recName pat suslikParams branchPredName branch =
  let
    patAsn = applyLayoutPattern layout suslikParams pat

    suslikBranch =
      MkSuSLikBranch
      { suslikBranchCond = genBaseCond suslikParams patAsn
      , suslikBranchRhs = toHeaplets patAsn <>
          case defBranchGuardeds branch of
            [MkGuardedExpr (BoolLit True) body] -> toHeaplets $ lower' layoutDefs layout suslikParams body
            _ -> []
      }
  in
  suslikBranch

nontrivialBranch :: DefBranch -> Bool
nontrivialBranch branch =
  case defBranchGuardeds branch of
    [MkGuardedExpr (BoolLit True) _] -> False
    _ -> True

genDefPreds :: [Layout] -> Layout -> Def -> [InductivePred]
genDefPreds defs layout fnDef =
  let branchNames = map (genBranchName (defName fnDef)) [1..length (defBranches fnDef)]
      branchesWithNames = zip branchNames $ defBranches fnDef

      suslikParams = layoutSuSLikParams layout

      baseBranches =
        map (\(name, branch) -> genBaseBranch defs layout (defName fnDef) (defBranchPattern branch) (layoutSuSLikParams layout) name branch) branchesWithNames

      condPreds =
        map (\(name, branch) -> genCondPred defs layout (defName fnDef) name branch []) $ filter (nontrivialBranch . snd) branchesWithNames

      -- condBranches =

      basePred =
        MkInductivePred
        { inductivePredName = defName fnDef
        , inductivePredParams = map (locParam . nameToString) suslikParams
        , inductivePredBranches = baseBranches
        }
  in
  basePred : condPreds

genDefBranchPreds :: [Layout] -> String -> DefBranch -> [InductivePred]
genDefBranchPreds layoutDefs topLevelName branch = undefined

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
                          (PointsTo (Var (suslikName "x") :+ 1) (Var (freeVar "nxt"))
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

