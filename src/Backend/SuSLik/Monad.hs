-- | Monad for generating SuSLik code

{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}

module Backend.SuSLik.Monad
  where

import           Backend.SuSLik.SSL

import           Control.Monad.State

import           Data.List


data SuSLikEnv a b =
  SuSLikEnv
    { indPredNames :: [(a, b)] -- | Maps fun-SuSLik names to their inductive predicate names
    , uniq :: Int
    }

envExtend :: a -> b -> SuSLikEnv a b -> SuSLikEnv a b
envExtend fnName indPred e
  = e { indPredNames = (fnName, indPred) : indPredNames e }

envLookup :: Eq a => a -> SuSLikEnv a b -> Maybe b
envLookup fnName = lookup fnName . indPredNames

envEmpty :: SuSLikEnv a b
envEmpty = SuSLikEnv mempty 0

newtype SuSLik a b r
  = SuSLik (State (SuSLikEnv a b) r)
  deriving (Functor, Applicative, Monad, MonadState (SuSLikEnv a b))

runSuSLik :: SuSLik a b r -> (r, SuSLikEnv a b)
runSuSLik (SuSLik s) = runState s envEmpty

setIndPredName :: a -> b -> SuSLik a b ()
setIndPredName fnName = modify . envExtend fnName

getIndPredName :: (Show a, Eq a) => a -> SuSLik a b b
getIndPredName fnName =
  fmap (envLookup fnName) get >>= \case
    Nothing -> error $ "getIndPredName: cannot find " ++ show fnName
    Just str -> pure str

freshen :: String -> SuSLik a b String
freshen str = do
  currUniq <- uniq <$> get
  let newStr = str <> "_" <> show currUniq
  modify $ \e -> e { uniq = succ currUniq }
  pure newStr

