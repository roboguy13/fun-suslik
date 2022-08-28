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

data DefBranch =
  MkDefBranch
  { defBranchPattern :: Pattern String
  , defBranchGuardeds :: [GuardedExpr]
  }

data GuardedExpr =
  MkGuardedExpr
  { guardedCond :: Expr String
  , guardedBody :: Expr String
  }

defToSuSLikPreds :: Def -> [InductivePred]
defToSuSLikPreds = undefined

