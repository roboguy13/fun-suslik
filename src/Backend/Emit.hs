{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Backend.Emit
  where

import           Data.List
import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Semigroup (sconcat)

data Emitted a
  = EmitPart a
  | EmitJuxt (Emitted a) (Emitted a)
  | EmitBlock a a [Emitted a]

emitLine :: Emitted String -> Emitted String
emitLine x = EmitBlock "" "" [x]

instance Semigroup (Emitted a) where
  (<>) = EmitJuxt

-- data WithParens = NoParens | WithParens


class Emit a where
  emit :: a -> String

-- withParens :: Emitted String -> Emitted String
-- withParens x = emitJuxt [EmitPart "(", x, EmitPart ")"]

intercalateS :: Semigroup s => s -> s -> [s] -> s
intercalateS whenEmpty _ [] = whenEmpty
intercalateS _ xs lists@(_:_) =
  case intersperse xs lists of
    (ys:yss) -> sconcat (ys :| yss)

-- emitJuxt :: [Emitted a] -> Emitted a
-- emitJuxt = foldr1 EmitJuxt
--
-- emitBinOp :: (Emit a, Emit b) => String -> a -> b -> Emitted String
-- emitBinOp op x y = emitJuxt [withParens (emit x), EmitPart op, withParens (emit x)]
--
-- emitString :: Emit a => a -> String
-- emitString = emitString' . emit
--
-- emitString' :: Emitted String -> String
-- emitString' (EmitPart x) = x
-- emitString' (EmitJuxt x y) =
--   unwords
--     [emitString' x
--     ,emitString' y
--     ]
-- emitString' (EmitBlock start end block) =
--   unlines'
--     [start
--     ,unlines' $ map (("  " <>) . emitString') block
--     ,end
--     ]

instance Emit String where emit = id

unlines' :: [String] -> String
unlines' = intercalate "\n"

indent :: String -> String
indent = indentLines . lines

indentLines :: [String] -> String
indentLines = unlines' . map ("  "<>)

emitBinOp :: (Emit a, Emit b) => String -> a -> b -> String
emitBinOp op x y = emit x <> " " <> op <> " " <> emit y

withParens :: String -> String
withParens x = "(" <> x <> ")"

