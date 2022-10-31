module Syntax.Simple.Test
  where

import           Syntax.Simple.Parse
import           Syntax.Simple.Def
import           Syntax.Simple.Expr
import           Syntax.Ppr

test1' :: Def
test1' =
  parse' parseFnDef
    "filterLt7 : List -> List;\
    \filterLt7 (Nil) := Nil;\
    \filterLt7 (Cons head tail)\
    \  | head < 7       := Cons head (filterLt7 tail)\
    \  | not (head < 7) := filterLt7 tail;"
    

leftListTest' :: Def
leftListTest' =
  parse' parseFnDef
    "leftList : Tree -> List;\
    \leftList (Leaf) := Nil;\
    \leftList (Node a left right) := Cons a (leftList left);"

evenTest' :: Def
evenTest' =
  parse' parseFnDef
    "even : List -> List;\
    \even (Nil) := Nil;\
    \even (Cons head tail) := odd tail;"

oddTest' :: Def
oddTest' =
  parse' parseFnDef
    "odd : List -> List;\
    \odd (Nil) := Nil;\
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
    "sum : List -> Int;\
    \sum (Nil) := 0;\
    \sum (Cons head tail) := head + (sum tail);"

foldTestTailRec :: Def
foldTestTailRec =
  parse' parseFnDef
    "sumTR : List -> Int -> Int;\
    \sumTR (Nil) acc := acc;\
    \sumTR (Cons head tail) acc := sumTR tail (head + acc);"

