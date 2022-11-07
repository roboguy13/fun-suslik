{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- {-# OPTIONS_GHC -Wall #-}

module Syntax.Name
  (Name_ (..)
  ,Name
  ,mangle
  ,unmangle
  ,FsName
  ,fsName
  ,SuSLikName
  ,ParamIndex (..)
  ,setNameIndex
  ,shiftName
  ,boundVar
  ,freeVar
  ,toNames
  ,maxUniq
  -- ,fsName
  -- ,suslikName
  )
  -- (SuSLikName
  -- ,FsName
  -- ,Name(..)
  -- ,suslikName
  -- ,fsName
  -- ,HeapEnv(..)
  -- ,Named(..)
  -- ,toSuSLikName
  -- ,substFsName
  -- ,NameSupply
  -- ,runNameSupply
  -- ,freshen
  -- )
  where

-- import           Bound
import           Bound.Scope

import           Control.Monad.State

import           Data.Maybe

import           Syntax.Ppr

-- TODO: Store unique IDs in the two name types?

-- newtype SuSLikName = MkSuSLikName { getSuSLikName :: String }
--   deriving (Eq, Ord, Show)

-- data FsName where
--   MkFsName :: String -> FsName
--   deriving (Eq, Ord, Show)

data Name_ a where
  MkName :: a -> Name_ a
  MkFree :: Int -> a -> Name_ a
  MkInternal :: Int -> Name_ a
  deriving (Show, Eq, Ord)

type Name = Name_ String

type SuSLikName = String --Name
type FsName = String --Name

mangle :: String -> String
mangle = ('$':)

unmangle :: String -> String
unmangle ('$':xs) = xs

fsName :: FsName -> String
fsName = id

maxUniq :: (Functor f, Foldable f) => f (Name_ a) -> Int
maxUniq = fromMaybe 0 . maximum . fmap getNameIndex

shiftName :: Name_ a -> Name_ a
shiftName (MkFree i x) = MkFree (succ i) x
shiftName n = n

getNameIndex :: Name_ a -> Maybe Int
getNameIndex (MkFree i _) = Just i
getNameIndex _ = Nothing

setNameIndex :: Int -> Name_ a -> Name_ a
setNameIndex i (MkFree _ x) = MkFree i x
setNameIndex _ n = n

boundVar :: a -> Name_ a
boundVar = MkName

freeVar :: a -> Name_ a
freeVar = MkFree 0

toNames :: Functor f => Int -> [String] -> f String -> f Name
toNames level boundVars = fmap go
  where
    go x =
      if x `elem` boundVars
        then MkName x
        else MkFree level x

newtype ParamIndex = MkParamIndex Int
  deriving (Show, Eq, Ord, Enum)

instance Ppr a => Ppr (Name_ a) where
  ppr (MkName n) = "_" <> ppr n
  ppr (MkFree i n) = "_" <> ppr n <> show i
  ppr (MkInternal i) = "v" <> show i
  -- SuSLikNm :: SuSLikName -> Name
  -- FsNm :: FsName -> Name
  -- deriving (Show)

-- instance Ppr SuSLikName where
--   ppr = genString
--
-- instance Ppr FsName where
--   ppr = genString
--
-- data HeapEnv b = MkHeapEnv [SuSLikName]
--
-- fsName :: String -> FsName
-- fsName = MkFsName
--
-- suslikName :: String -> SuSLikName
-- suslikName = MkSuSLikName
--
-- class Named a where
--   toFsName :: a -> FsName
--   genString :: a -> String
--   freshenWith :: Int -> a -> a
--
-- instance Named Name where
--   toFsName (FsNm n) = n
--   toFsName (SuSLikNm n) = toFsName n
--
--   genString (FsNm n) = genString n
--   genString (SuSLikNm n) = genString n
--
--
-- instance Named FsName where
--   toFsName = id
--
--   genString (MkFsName str) = "fs_" <> str
--   genString (FromSuSLikName name) = genString name
--
--   freshenWith uniq (MkFsName str) = MkFsName (str <> show uniq)
--   freshenWith uniq (FromSuSLikName name) =
--     FromSuSLikName $ freshenWith uniq name
--
-- instance Named SuSLikName where
--   toFsName = FromSuSLikName
--
--   genString = ("sus_"<>) . getSuSLikName
--   freshenWith uniq (MkSuSLikName str) = MkSuSLikName (str <> show uniq)
--
-- toSuSLikName :: FsName -> SuSLikName
-- toSuSLikName (FromSuSLikName name) = name
-- toSuSLikName (MkFsName str) = MkSuSLikName str
--
-- -- TODO: Do we need to mangle the SuSLik names when turning them into
-- -- FsNames to avoid name capture?
-- substFsName :: (Monad m, Named a) => m a -> Scope n m FsName -> m FsName
-- substFsName = instantiate1 . fmap toFsName
--
-- newtype NameSupply a =
--   MkNameSupply (State Int a)
--   deriving (Functor, Applicative, Monad, MonadState Int)
--
-- runNameSupply :: NameSupply a -> a
-- runNameSupply (MkNameSupply m) =
--   evalState m 0
--
-- freshen :: Named a => a -> NameSupply a
-- freshen named = do
--   uniq <- get
--   modify succ
--   pure (freshenWith uniq named)

