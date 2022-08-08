module Representation.Parts
  where

import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Foldable

data Parts a
  = Leaf a
  | Parts (NonEmpty (Parts a)) (NonEmpty a -> a)

instance Eq a => Eq (Parts a) where
  x == y = rebuild x == rebuild y

instance Ord a => Ord (Parts a) where
  compare x y = compare (rebuild x) (rebuild y)

instance Show a => Show (Parts a) where
  show = show . rebuild

rebuild :: Parts a -> a
rebuild (Parts cs f) = f $ fmap rebuild cs
rebuild (Leaf x) = x

partsChildren :: Parts a -> [Parts a]
partsChildren (Parts xs _) = toList xs
partsChildren (Leaf _) = []

overParts :: (Parts a -> Parts a) -> Parts a -> Parts a
overParts f (Parts xs g) = Parts (fmap f xs) g
overParts f (Leaf x) = f (Leaf x)

class ToParts n where
  toParts :: n -> Parts n

  nodeChildren :: n -> [n] -- This must eventually give back the empty list
  nodeChildren = map rebuild . partsChildren . toParts


fromParts :: Parts n -> n
fromParts (Parts cs f) = f (fmap fromParts cs)
fromParts (Leaf x) = x

