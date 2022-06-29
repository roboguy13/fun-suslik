module Error.Render
  (renderTcError, renderAnnotated, (<+>), unlines')
  where

import           Data.List
import           Data.Char

import           Error.Error
import           Nucleus.Expr
import           Nucleus.TypeChecker

-- source text goes here
-- ^~~~~~ ^~~~
-- |      |____ Message for "text"
-- |___________ Message for "source"
--
--

renderTcError :: String -> TcError -> String
renderTcError sourceLine = renderAnnotated . annotateTcError sourceLine

-- | Precondition: Argument is sorted on span start index
spansToSpaceCount :: [(SrcSpan, Message)] -> [(Int, Message)]
spansToSpaceCount = go 0 0
  where
    go ix spaceAcc [] = []
    go ix spaceAcc ((span, msg):rest)
      | ix == spanStart span = (spaceAcc, msg) : go (ix + spanLength span) (spanLength span-1) rest
      | otherwise            = go (ix + 1) (spaceAcc + 1) ((span, msg):rest)

getMessageInits :: [Segment] -> [[Segment]]
getMessageInits = reverse . drop 1 . inits . dropWhileEnd (not . hasMessage) . go
  where
    -- Drop spaces
    go :: [Segment] -> [Segment]
    go (SegmentSpace str1:SegmentSpace str2:rest) = go (SegmentSpace (str1++str2) : rest)
    go (SegmentSpace spaces:Segment segSrc msg:rest) = Segment segSrc msg : go rest
    go (x:xs) = x : go xs
    go [] = []

mapButLast :: (a -> a) -> [a] -> [a]
mapButLast _ [] = []
mapButLast _ [x] = [x]
mapButLast f (x:xs) = f x : mapButLast f xs

renderDownParts :: [(SrcSpan, Message)] -> [String]
renderDownParts = map (concat . mapButLast (++"\x2502") . map go) . reverse . inits . spansToSpaceCount
  where
    go (n, _) = replicate n ' ' -- |

-- renderDownParts :: [Segment] -> [String]
-- renderDownParts = map (dropWhileEnd isSpace . concat . map renderPart) . getMessageInits
--   where
--     renderPart (SegmentSpace str) = str
--     renderPart seg
--       | hasMessage seg = '|' : replicate (segmentLength seg) ' '
--       | otherwise      = replicate (segmentLength seg) ' '

onLast :: (a -> a) -> [a] -> [a]
onLast _ [] = []
onLast f [x] = [f x]
onLast f (x:xs) = x : onLast f xs

renderAcrossParts :: [(SrcSpan, Message)] -> [String]
renderAcrossParts = map (connector++) . map go . incr 0 . reverse . scanr (+) 1 . map fst . spansToSpaceCount
  where
    connector = "\x2514"
    go n = replicate (n+1) '\x2500' -- _

    incr _ [] = []
    incr n (x:xs) = (x+n) : incr (n+1) xs

-- renderAcrossParts :: [Segment] -> [String]
-- renderAcrossParts segs0 = onLast ("___" <>) $ map go colOffsets
--   where
--     segs = map (sourceMap (dropWhile isSpace)) $ getMessageInits segs0 !! 0

--     go colOffset = replicate (colOffset) '_'

--     segLens = map segmentLength segs

--     colOffsets = reverse . drop 1 . scanl (-) (sum segLens+2) $ segLens

renderHighlights :: [Segment] -> String
renderHighlights segs = concatMap go segs
  where
    go (SegmentSpace str) = str
    go s
      | hasMessage s = '\x250D' : replicate (segmentLength s - 1) '\x2501'
      | otherwise    = replicate (segmentLength s) ' '

(<+>) :: Semigroup a => [a] -> [a] -> [a]
xss <+> yss = zipWith (<>) xss yss

unlines' :: [String] -> String
unlines' = intercalate "\n"

renderAnnotated :: Annotated -> String
renderAnnotated ann@(Annotated segs) =
  let spans = getSpans ann
  in
  unlines'
    [ plainSource ann
    , renderHighlights segs
    , unlines' (
          renderDownParts spans
          <+> renderAcrossParts spans
          <+> (map ((" "<>) . showMessage)
                   (reverse (getExistingMessages ann)))
        )
    ]

withColor :: String -> Color -> Message
withColor = flip Message

defaultColor :: String -> Message
defaultColor = (`withColor` DefaultColor)

greenColor :: String -> Message
greenColor = (`withColor` Green)

yellowColor :: String -> Message
yellowColor = (`withColor` Yellow)

redColor :: String -> Message
redColor = (`withColor` Red)

blueColor :: String -> Message
blueColor = (`withColor` Blue)

resetColor :: String
resetColor = "\ESC[0m"

-- setBgColor :: Color -> String
-- setBgColor DefaultColor = resetColor
-- setBgColor Green = "\ESC[42m"
-- setBgColor Yellow = "\ESC[43m"

setFgColor :: Color -> String
setFgColor DefaultColor = resetColor
setFgColor Red = "\ESC[31;1m"
setFgColor Green = "\ESC[32;1m"
setFgColor Yellow = "\ESC[33;1m"
setFgColor Blue = "\ESC[34;1m"

setBlackText :: String
setBlackText = "\ESC[30m"

showMessage :: Message -> String
showMessage msg = setFgColor (messageColor msg) <> messageString msg <> resetColor

