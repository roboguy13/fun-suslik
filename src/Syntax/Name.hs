{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# OPTIONS_GHC -Wall #-}

module Syntax.Name
  (SuSLikName
  ,FsName
  ,suslikName
  ,fsName
  ,HeapEnv(..)
  ,Named(..)
  ,toSuSLikName
  ,substFsName
  ,NameSupply
  ,runNameSupply
  ,freshen
  )
  where

-- import           Bound
import           Bound.Scope

import           Control.Monad.State

import           Syntax.Ppr

-- TODO: Store unique IDs in the two name types?

newtype SuSLikName = MkSuSLikName { getSuSLikName :: String }
  deriving (Eq, Ord, Show)

data FsName where
  MkFsName :: String -> FsName
  FromSuSLikName :: SuSLikName -> FsName
  deriving (Eq, Ord, Show)

instance Ppr SuSLikName where
  ppr = genString

instance Ppr FsName where
  ppr = genString

data HeapEnv b = MkHeapEnv [SuSLikName]

fsName :: String -> FsName
fsName = MkFsName

suslikName :: String -> SuSLikName
suslikName = MkSuSLikName

class Named a where
  toFsName :: a -> FsName
  genString :: a -> String
  freshenWith :: Int -> a -> a

instance Named FsName where
  toFsName = id

  genString (MkFsName str) = "fs_" <> str
  genString (FromSuSLikName name) = genString name

  freshenWith uniq (MkFsName str) = MkFsName (str <> show uniq)
  freshenWith uniq (FromSuSLikName name) =
    FromSuSLikName $ freshenWith uniq name

instance Named SuSLikName where
  toFsName = FromSuSLikName

  genString = ("sus_"<>) . getSuSLikName
  freshenWith uniq (MkSuSLikName str) = MkSuSLikName (str <> show uniq)

toSuSLikName :: FsName -> SuSLikName
toSuSLikName (FromSuSLikName name) = name
toSuSLikName (MkFsName str) = MkSuSLikName str

-- TODO: Do we need to mangle the SuSLik names when turning them into
-- FsNames to avoid name capture?
substFsName :: (Monad m, Named a) => m a -> Scope n m FsName -> m FsName
substFsName = instantiate1 . fmap toFsName

newtype NameSupply a =
  MkNameSupply (State Int a)
  deriving (Functor, Applicative, Monad, MonadState Int)

runNameSupply :: NameSupply a -> a
runNameSupply (MkNameSupply m) =
  evalState m 0

freshen :: Named a => a -> NameSupply a
freshen named = do
  uniq <- get
  modify succ
  pure (freshenWith uniq named)

