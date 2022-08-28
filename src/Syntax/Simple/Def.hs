module Syntax.Simple.Def
  where

import           Syntax.Simple.Expr
import           Syntax.Simple.SuSLik
import           Syntax.Name

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
toSuSLikExpr (Var v) = VarS $ toSuSLikName v
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
  MkLayout
  { layoutName = "sll"
  , layoutAdtName = "List"
  , layoutSuSLikParams = [suslikName "x"]
  , layoutBranches = [ (MkPattern "Nil" [], [])
                     , (MkPattern "Cons" [fsName "head", fsName "tail"]
                       ,[PointsTo (Here $ suslikName "x") (fsName "head")
                        ,PointsTo (suslikName "x" :+ 1) (fsName "nxt")
                        ,HeapletApply "sll" [suslikName "nxt"] (fsName "tail")
                        ]
                       )
                     ]
  }

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

