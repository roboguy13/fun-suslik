import Criterion.Main

import Control.DeepSeq
import GHC.Generics

data Tree = Empty | Branch Int Tree Tree
  deriving (Generic)

instance NFData Tree

data List = Cons Int List | Nil
  deriving (Generic)

instance NFData List

range :: Int -> Int -> List
range start end
  | start >= end = Nil
  | otherwise    = Cons start (range (start + 1) end)

tree_byheight :: Int -> Int -> Tree
tree_byheight start end
  | start >= end = Empty
  | otherwise    = Branch start (tree_byheight (start + 1) end) (tree_byheight (start + 1) end)

tree_plus1 :: Tree -> Tree
tree_plus1 Empty = Empty
tree_plus1 (Branch a b c) = Branch (a+1) (tree_plus1 b) (tree_plus1 c)

main :: IO ()
main =
  let t1 = tree_byheight 1 20
    in
  defaultMain
    [ bgroup "tree_plus1"
        [ bench "1" $ nf (\(xs) -> tree_plus1 xs) (t1)
        ]
    ]