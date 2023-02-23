import Criterion.Main

import Control.DeepSeq
import GHC.Generics

data List = Cons Int List | Nil
  deriving (Generic)

instance NFData List

range :: Int -> Int -> List
range start end
  | start >= end = Nil
  | otherwise    = Cons start (range (start + 1) end)

myapp :: List -> List -> List
myapp Nil ys = ys
myapp (Cons x xs) ys = Cons x (myapp xs ys)

main :: IO ()
main =
  let l1 = range 1 100000
      l2 = range 1 100000
  in
  defaultMain
    [ bgroup "myapp"
        [ bench "1" $ nf (\(xs, ys) -> myapp xs ys) (l1, l2)
        ]
    ]