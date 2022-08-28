module Syntax.Ppr
  where

class Ppr a where
  ppr :: a -> String

instance Ppr Int where ppr = show
instance Ppr Bool where ppr = show

