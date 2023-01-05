{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

module Syntax.Simple.Defunctionalize (defunctionalize) where

import Control.Monad.State
import Data.List
import Data.Void
import Syntax.FreshGen
import Syntax.Simple.Heaplet

defunctionalize :: [ElaboratedDef] -> [Layout] -> ElaboratedDef -> [ElaboratedDef]
defunctionalize globals layouts origDef = origDef : go origDef
  where
    defGo def =
      def
        { defBranches = map branchGo (defBranches def)
        }

    branchGo branch =
      branch
        { defBranchGuardeds = map goGuarded (defBranchGuardeds branch)
        }

    goGuarded (MkGuardedExpr cond body) =
      MkGuardedExpr (go cond) (go body)

    go = undefined

newtype Defun a = MkDefun (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

runDefun :: Defun a -> a
runDefun (MkDefun m) = evalState m 0

defunctionalizedName :: String -> [String] -> Defun String
defunctionalizedName fnName fnArgs = do
  uniq <- get
  modify succ
  pure (fnName ++ "__df_" ++ intercalate "_" fnArgs ++ show uniq)

substFnApply :: String -> String -> ElaboratedDef -> ElaboratedDef
substFnApply oldName newName def =
  def
    { defBranches = map branchGo (defBranches def)
    }
  where
    branchGo branch =
      branch
        { defBranchGuardeds = map goGuarded (defBranchGuardeds branch)
        }

    goGuarded (MkGuardedExpr cond body) =
      MkGuardedExpr (go cond) (go body)

    go :: ElaboratedExpr String -> ElaboratedExpr String
    go (Lower ty _) = absurd ty
    go (Instantiate _ x _ _) = absurd x
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
    go (Apply fName0 outLayout inLayouts args) =
      let fName =
            if fName0 == oldName
              then newName
              else fName0
       in Apply fName outLayout inLayouts (map go args)
    go (ConstrApply ty cName args) =
      ConstrApply ty cName (map go args)
