-- | Shifting for de Bruijn indices

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax.Simple.Shift
  where

import           Syntax.Name

import           Control.Monad.State

data Shift f a = Shift (f (Name_ a))

newtype Leveled a = Leveled (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

runLeveled :: Leveled a -> a
runLeveled (Leveled m) = evalState m 0

newUniq :: Leveled Int
newUniq = do
  i <- get
  modify succ
  pure i

shift :: Functor f => Shift f a -> Leveled (f (Name_ a))
shift (Shift x) = do
  i <- newUniq 
  -- modify succ
  pure $ fmap (setNameIndex i) x

