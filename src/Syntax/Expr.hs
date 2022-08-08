module Syntax.Expr
  where

import           Bound
import           Bound.Scope

data FsExpr p a
  = FsVar p a

  | FsInt p Int
  | FsBool p Bool

  | FsLam p (Scope () (FsExpr p) a)
  | FsLet p (FsExpr p a) (Scope () (FsExpr p) a)
  | FsCase p (FsExpr p a) [FsAlt p a]

  | FsApp p (FsExpr p a) (FsExpr p a)

  | FsAdd p (FsExpr p a) (FsExpr p a)
  | FsSub p (FsExpr p a) (FsExpr p a)
  | FsMul p (FsExpr p a) (FsExpr p a)

  | FsLt p (FsExpr p a) (FsExpr p a)
  | FsEq p (FsExpr p a) (FsExpr p a)
  | FsNot p (FsExpr p a) (FsExpr p a)
  | FsAnd p (FsExpr p a) (FsExpr p a)
  | FsOr p (FsExpr p a) (FsExpr p a)

  | FsFoldr p (FsExpr p a) (FsExpr p a) (FsExpr p a)
  | FsFilter p (FsExpr p a) (FsExpr p a)

data FsAlt p a
  = FsAltNoParams p (FsExpr p a)
  | FsAltParam p (Scope () (FsAlt p) a)

data FsType p a
  = FsFunTy p (FsType p a) (FsType p a)
  | FsIntTy p
  | FsBoolTy p
  | FsLayoutTy p (FsLayoutType p a)

-- | Types of the form @T >-> layout[x,y,...]@
data FsLayoutType p a =
  MkFsLayoutType
  { fsLayoutTypeP :: p
  , fsLayoutSource :: FsType p a
  , fsLayoutTargetFVs :: [a]
  }

