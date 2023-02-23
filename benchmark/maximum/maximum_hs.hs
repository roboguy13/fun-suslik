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

mymax :: List -> Int
mymax Nil = -1
mymax (Cons x xs) = 
  let i = mymax xs in
  if i < x
    then x
    else i

main :: IO ()
main =
  let l1 = range 1 100000
    in
  defaultMain
    [ bgroup "mymax"
        [ bench "1" $ nf (\(xs) -> mymax xs) (l1)
        ]
    ]