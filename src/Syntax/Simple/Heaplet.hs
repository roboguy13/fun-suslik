{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GADTs #-}

module Syntax.Simple.Heaplet
  where

import           Syntax.Name

import           Text.Show.Deriving
import           Data.Functor.Classes

type LayoutBranch' = LayoutBranch FsName SuSLikName

data Heaplet a b where
  PointsTo :: Loc b -> a -> Heaplet a b
  HeapletApply :: String -> [b] -> a -> Heaplet a b
  deriving (Show)

data Loc a = Here a | a :+ Int
  deriving (Show, Functor, Foldable, Traversable)

newtype LayoutBranch a b = MkLayoutBranch [Heaplet a b]
  deriving (Show)

$(deriveShow1 ''Loc)
$(deriveShow1 ''Heaplet)
$(deriveShow1 ''LayoutBranch)

