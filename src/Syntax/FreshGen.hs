{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax.FreshGen
  where

import           Control.Monad.State

import           Syntax.Name

newtype FreshGen a = FreshGen (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

runFreshGen :: FreshGen a -> ([Name_ b], a)
runFreshGen (FreshGen m) =
  case runState m 0 of
    (r, maxUniq) -> (map MkInternal [0..maxUniq-1], r)

getFresh :: FreshGen (Name_ b)
getFresh = do
  curr <- get
  modify succ
  return $ MkInternal curr

getUniq :: FreshGen Int
getUniq = do
  curr <- get
  modify succ
  pure curr

