{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Syntax.Ppr
  where

class Ppr a where
  ppr :: a -> String

pprBinOp :: (Ppr a, Ppr b) => String -> a -> b -> String
pprBinOp op x y = "(" ++ ppr x ++ " " ++ op ++ " " ++ ppr y ++ ")"

instance Ppr Int where ppr = show
instance Ppr Bool where ppr = show
instance Ppr String where ppr = id

