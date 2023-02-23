import Criterion.Main

import Control.DeepSeq
import GHC.Generics

data List = Cons Int List | Nil
  deriving (Generic)

instance NFData List

range :: Int -> Int -> List
range start end
  | start >= end = Nil
  | otherwise    = Cons 1 (range (start + 1) end)

mysum :: List -> Int
mysum Nil = 0
mysum (Cons head tail) = head + (mysum tail)

main :: IO ()
main =
  let l1 = range 1 100000
    in
  defaultMain
    [ bgroup "mysum"
        [ bench "1" $ nf (\(xs) -> mysum xs) (l1)
        ]
    ]