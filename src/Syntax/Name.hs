{-# LANGUAGE GADTs #-}

{-# OPTIONS_GHC -Wall #-}

module Syntax.Name
  (SuSLikName
  ,FsName
  ,suslikName
  ,fsName
  ,HeapEnv(..)
  ,Named(..)
  ,substFsName
  )
  where

-- import           Bound
import           Bound.Scope

newtype SuSLikName = MkSuSLikName { getSuSLikName :: String }
  deriving (Eq, Ord, Show)

data FsName where
  MkFsName :: String -> FsName
  FromSuSLikName :: SuSLikName -> FsName
  deriving (Eq, Ord, Show)

data HeapEnv b = MkHeapEnv [SuSLikName]

fsName :: String -> FsName
fsName = MkFsName

suslikName :: String -> SuSLikName
suslikName = MkSuSLikName

class Named a where
  toFsName :: a -> FsName
  genString :: a -> String

instance Named FsName where
  toFsName = id

  genString (MkFsName str) = "fs_" <> str
  genString (FromSuSLikName name) = genString name

instance Named SuSLikName where
  toFsName = FromSuSLikName

  genString = ("sus_"<>) . getSuSLikName

-- TODO: Do we need to mangle the SuSLik names when turning them into
-- FsNames to avoid name capture?
substFsName :: (Monad m, Named a) => m a -> Scope n m FsName -> m FsName
substFsName = instantiate1 . fmap toFsName

