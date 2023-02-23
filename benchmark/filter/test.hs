import Criterion.Main
import Text.Printf
import Control.DeepSeq
import GHC.Generics

data List = Cons Int List | Nil
  deriving (Generic)

instance NFData List

range :: Int -> Int -> List
range start end
  | start >= end = Nil
  | otherwise    = Cons start (range (start + 1) end)

filterLt9  :: List -> List
filterLt9  Nil = Nil
filterLt9  (Cons x xs) 
  | x < 50000 = (Cons x (filterLt9 xs))
  | otherwise = (filterLt9 xs)


main :: IO ()
main =
  let l1 = range 1 100000
    in
  (filterLt9 l1)