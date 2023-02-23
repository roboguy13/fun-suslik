import Criterion.Main

import Control.DeepSeq
import GHC.Generics

data List = Cons Int List | Nil
  deriving (Generic)

instance NFData List

data Mlist = LCons List Mlist | LNil
  deriving (Generic)

instance NFData Mlist

range :: Int -> Int -> List
range start end
  | start >= end = Nil
  | otherwise    = Cons start (range (start + 1) end)

multi_range :: Int -> Int -> Mlist
multi_range x y
  | x == 0 = LNil
  | otherwise = LCons (range 1 y) (multi_range (x-1) y)

mysum :: List -> Int
mysum Nil = 0
mysum (Cons head tail) = head + (mysum tail)

mapSum :: Mlist -> List
mapSum LNil = Nil
mapSum (LCons xs xss) = Cons (mysum xs) (mapSum xss)



main :: IO ()
main =
  let l1 = multi_range 1000 1000
    in
  defaultMain
    [ bgroup "mapSum"
        [ bench "1" $ nf (\(xs) -> mapSum xs) (l1)
        ]
    ]