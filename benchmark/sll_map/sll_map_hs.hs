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

sll_plus1 :: List -> List
sll_plus1 Nil = Nil
sll_plus1 (Cons x xs) = (Cons (x + 1) (sll_plus1 xs))

main :: IO ()
main =
  let l1 = range 1 100000
    in
  defaultMain
    [ bgroup "sll_plus1"
        [ bench "1" $ nf (\(xs) -> sll_plus1 xs) (l1)
        ]
    ]