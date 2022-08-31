module Syntax.BiScope
  where

import           Bound
import           Bound.Scope

import           Data.Functor.Compose

newtype BiScope p a b r =
  MkBiScope (Scope a (Compose (Scope b) p) r)
  -- MkBiScope (Scope a (Scope b (p a)) r)

