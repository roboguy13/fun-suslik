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

toSuSLikExpr :: Expr FsName -> SuSLikExpr SuSLikName
toSuSLikExpr (Var v) = VarS v
toSuSLikExpr (BoolLit b) = BoolS b
toSuSLikExpr (And x y) = AndS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Or x y) = OrS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Not x) = NotS (toSuSLikExpr x)
toSuSLikExpr (Add x y) = AndS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Sub x y) = SubS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Mul x y) = MulS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Equal x y) = EqualS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Lt x y) = LtS (toSuSLikExpr x) (toSuSLikExpr y)
toSuSLikExpr (Le x y) = LeS (toSuSLikExpr x) (toSuSLikExpr y)

genBranchName :: String -> Int -> String
genBranchName str i = str <> show i

genBaseCond :: [String] -> Assertion' String -> SuSLikExpr String
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

toHeaplets :: Assertion' a -> [Heaplet a]
toHeaplets Emp = []
toHeaplets (PointsTo x y rest) = PointsToS (fmap getVar x) (getVar y) : toHeaplets rest
toHeaplets (HeapletApply str suslikArgs _ rest) =
  HeapletApplyS str (map getVar suslikArgs) : toHeaplets rest

genPatternHeaplets :: [Layout] -> Layout -> Pattern FsName -> [Heaplet String]
genPatternHeaplets layoutDefs layout (MkPattern cName args) =
    -- TODO: Avoid capture here between the SuSLik parameters and the FS
    -- variables
  toHeaplets $ fmap (fmap nameToString) $ applyLayout 0 layout (layoutSuSLikParams layout) cName $ map Var args

genBaseBranch :: [Layout] -> Pattern FsName -> [String] -> Assertion' String -> (SuSLikBranch, Maybe InductivePred)
genBaseBranch layoutDefs pat suslikParams branchAsn =
  let
    suslikBranch =
      MkSuSLikBranch
      { suslikBranchCond = genBaseCond suslikParams branchAsn
      }
  in
  undefined

genDefPreds :: [Layout] -> Layout -> Def -> [InductivePred]
genDefPreds layoutDefs layout fnDef =
  let branchNames = map (genBranchName (defName fnDef)) [1..length (defBranches fnDef)]

      suslikParams = layoutSuSLikParams layout

      baseBranches = undefined

      basePred =
        MkInductivePred
        { inductivePredName = defName fnDef
        , inductivePredParams = map (locParam . nameToString) suslikParams
        , inductivePredBranches = baseBranches
        }
  in
  undefined

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
  , defType = undefined
  , defBranches =
      [MkDefBranch (MkPattern "Nil" [])
          [MkGuardedExpr (BoolLit True)
            (ConstrApply "Nil" [])
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

