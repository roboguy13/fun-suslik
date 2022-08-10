-- | Monad for generating SuSLik code

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Backend.SuSLik.Monad
  where

import           Backend.SuSLik.SSL

import           Control.Monad.State

import           Data.List

-- | Maps fun-SuSLik names to their inductive predicate names
newtype SuSLikEnv = SuSLikEnv [(String, String)]

envExtend :: String -> String -> SuSLikEnv -> SuSLikEnv
envExtend fnName indPred (SuSLikEnv e)
  = SuSLikEnv ((fnName, indPred) : e)

envLookup :: String -> SuSLikEnv -> Maybe String
envLookup fnName (SuSLikEnv e) = lookup fnName e

envEmpty :: SuSLikEnv
envEmpty = SuSLikEnv mempty

newtype SuSLik a
  = SuSLik (State SuSLikEnv a)
  deriving (Functor, Applicative, Monad, MonadState SuSLikEnv)

runSuSLik :: SuSLik a -> (a, SuSLikEnv)
runSuSLik (SuSLik s) = runState s envEmpty

setIndPredName :: String -> String -> SuSLik ()
setIndPredName fnName = modify . envExtend fnName

getIndPredName :: String -> SuSLik String
getIndPredName fnName =
  fmap (envLookup fnName) get >>= \case
    Nothing -> error $ "getIndPredName: cannot find " ++ fnName
    Just str -> pure str

