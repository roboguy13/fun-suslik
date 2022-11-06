{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax.FreshGen
  where

import           Control.Monad.State
import           Control.Monad.Identity

import           Syntax.Name

newtype FreshGenT m a = FreshGen (StateT Int m a)
  deriving (Functor, Applicative, Monad, MonadState Int, MonadTrans)

type FreshGen = FreshGenT Identity

runFreshGen :: FreshGen a -> ([Name_ b], a)
runFreshGen = runIdentity . runFreshGenT

runFreshGenT :: Monad m => FreshGenT m a -> m ([Name_ b], a)
runFreshGenT (FreshGen m) = do
  (r, maxUniq) <- runStateT m 0
  pure (map MkInternal [0..maxUniq-1], r)

getFresh :: Monad m => FreshGenT m (Name_ b)
getFresh = do
  curr <- get
  modify succ
  return $ MkInternal curr

getFreshWith :: Monad m => String -> FreshGenT m String
getFreshWith name = do
  i <- getUniq
  pure $ (name <> show i)

getUniq :: Monad m => FreshGenT m Int
getUniq = do
  curr <- get
  modify succ
  pure curr

