module Syntax.Simple.Test
  where

import           Syntax.Simple.Parse
import           Syntax.Simple.Def
import           Syntax.Simple.Expr
import           Syntax.Simple.Heaplet
import           Syntax.Ppr

import           Text.Megaparsec

test1' :: Def
test1' =
  -- parse' (parseFnDef <* eof)
  parse' parseFnDef
    "filterLt7 : List -> List;\n\
    \filterLt7 (Nil) := Nil;\n\
    \filterLt7 (Cons head tail)\n\
    \  | head < 7       := Cons head (filterLt7 tail);\n\
    \  | not (head < 7) := filterLt7 tail;"

leftListTest' :: Def
leftListTest' =
  parse' parseFnDef
    "leftList : Tree -> List\n\
    \leftList (Leaf) := Nil\n\
    \leftList (Node a left right) := Cons a (leftList left);"

evenTest' :: Def
evenTest' =
  parse' parseFnDef
    "even : List -> List\n\
    \even (Nil) := Nil\n\
    \even (Cons head tail) := odd tail;"

oddTest' :: Def
oddTest' =
  parse' parseFnDef
    "odd : List -> List\n\
    \odd (Nil) := Nil\n\
    \odd (Cons head tail) := Cons head (even tail);"

-- wrapIntAdt :: Adt
-- wrapIntAdt =
--   parse' parseAdtDef
--     "data WrapInt := Wrapped Int"
--
-- wrapIntLayout :: Layout
-- wrapIntLayout =
--   parse' parseLayout
--     "WrapIntL : WrapInt >-> layout[x];\
--     \WrapIntL (Wrapped i) := x :-> i;"

foldTest :: Def
foldTest =
  parse' parseFnDef
    "sum : List -> Int\n\
    \sum (Nil) := 0\n\
    \sum (Cons head tail) := head + (sum tail);"

foldTestTailRec :: Def
foldTestTailRec =
  parse' parseFnDef
    "sumTR : List -> Int -> Int\n\
    \sumTR (Nil) acc := acc\n\
    \sumTR (Cons head tail) acc := sumTR tail (head + acc);"

replicateTest :: Def
replicateTest =
  parse' parseFnDef
    "replicate : Int -> Int -> List\n\
    \replicate n i\n\
    \ | n == 0 := Nil\n\
    \ | not (n == 0) := Cons i (replicate (n - 1) i);"

takeTest :: Def
takeTest =
  parse' parseFnDef
    "take : List -> Int -> List;\n\
    \take (Nil) i := Nil;\n\
    \take (Cons head tail) i\n\
    \| i == 0 := Nil;\n\
    \| not (i == 0) := Cons head (take tail) (i - 1);"

sllLayoutTest :: Layout
sllLayoutTest =
  parse' parseLayout
    "Sll : List >-> layout[x]\n\
    \Sll (Nil) := emp\n\
    \Sll (Cons head tail) := x :-> head, (x+1) :-> tail, Sll tail;"

treeLayoutTest :: Layout
treeLayoutTest =
  parse' parseLayout
    "TreeLayout : Tree >-> layout[x]\n\
    \TreeLayout (Leaf) := emp\n\
    \TreeLayout (Node payload left right) :=\n\
    \  x :-> payload,\n\
    \  (x+1) :-> left,\n\
    \  (x+2) :-> right,\n\
    \  TreeLayout left,\n\
    \  TreeLayout right;"

adtsTest :: [Adt]
adtsTest =
  parse' (parseSpaced parseAdtDef)
    "data List := Nil | Cons Int List;\n\
    \\n\
    \data Tree := Leaf | Node Int Tree Tree;"

