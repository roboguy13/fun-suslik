{-# LANGUAGE ExistentialQuantification #-}

module Syntax.Expr
  where

import           Bound
import           Bound.Scope

import           Data.List
import           Data.Ord

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
  = FsAltNoParams p (ConName p a) (FsExpr p a)
  | FsAltParams p (ConName p a) (Scope () (FsExpr p) a)

sortFsAlts :: Ord a => [FsAlt p a] -> [FsAlt p a]
sortFsAlts = sortBy (comparing fsAltConName)

type ConName p a = a

fsAltConName :: FsAlt p a -> ConName p a
fsAltConName (FsAltNoParams _ conName _) = conName
fsAltConName (FsAltParams _ conName _) = conName

data FsType p a
  = FsFunTy p (FsType p a) (FsType p a)
  | FsIntTy p
  | FsBoolTy p
  | FsLayoutTy p (FsLayoutType p a)

-- | Type of the form @T >-> layout[x,y,...]@
data FsLayoutType p a =
  MkFsLayoutType
  { fsLayoutTypeP :: p
  , fsLayoutSource :: FsType p a
  , fsLayoutTargetFVs :: [a]
  }

-- | Layout definition
data FsLayout p b a =
  MkFsLayout
  { fsLayoutP :: p
  , fsLayoutName :: String
  , fsLayoutType :: FsLayoutType p b
  , fsLayoutAlts :: [FsAlt p a]
  }

