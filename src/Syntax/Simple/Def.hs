{-# LANGUAGE OverloadedLists #-}

module Syntax.Simple.Def
  where

import           Syntax.Simple.Expr
import           Syntax.Simple.Heaplet
import           Syntax.Simple.SuSLik
import           Syntax.Name
import           Syntax.Ppr

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


genDefPreds :: [Layout] -> Def -> [InductivePred]
genDefPreds layoutDefs fnDef = undefined

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

testLower1 :: Assertion' FsName
testLower1 =
  applyLayout 0 sllLayout [MkName "z"]
    "Cons" [Var $ MkName "a",
      ConstrApply "Cons" [Var $ MkName "b",
        ConstrApply "Cons" [Var $ MkName "c", Var $ MkName "d"]]]


