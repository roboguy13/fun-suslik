{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Error.Error
  where

import           Data.List
import           Data.Maybe
import           Data.Char

import           Nucleus.Expr (SrcLoc (..), SrcSpan (..), spanLength)
import           Nucleus.TypeChecker

getSpanned :: ErrorMsgPart -> Maybe (SrcSpan, String)
getSpanned (ErrorMsgPart _ NoSrcLoc) = Nothing
getSpanned (ErrorMsgPart str (SrcLoc _ sp)) = Just (sp, str)

annotateTcError :: String -> TcError -> Annotated
annotateTcError sourceLine (TcError _basicMsg msgs) =
  annotate sourceLine $
    mapMaybe (fmap (fmap defMsg) . getSpanned) msgs

data Color = DefaultColor | Red | Green | Blue | Yellow
  deriving (Show, Eq)

data Message =
  Message
  { messageColor :: Color
  , messageString :: String
  }
  deriving (Show, Eq)

defMsg :: String -> Message
defMsg = Message DefaultColor

data Segment =
  Segment
  { segmentSource :: String
  , segmentMessage :: Maybe Message
  }
  | SegmentSpace String
  deriving (Show)

newtype Annotated = Annotated { getSegments :: [Segment] }
  deriving (Semigroup, Monoid, Show)

segSource :: String -> Segment
segSource str = Segment str Nothing

-- | NOTE: Duplicate indices will be ignored
annotate :: String -> [(SrcSpan, Message)] -> Annotated
annotate str0 msgs = Annotated $ go 0 "" str0
  where
    toSeg :: String -> [Segment]
    toSeg str
      | not (null str) =
          if all isSpace str
            then [SegmentSpace (reverse str)]
            else [Segment (reverse str) Nothing]
      | otherwise = []

    go :: Int -> String -> String -> [Segment]
    go ix soFar "" =
      toSeg soFar

    go ix soFar string@(c:cs) =
      case find ((== ix) . spanStart . fst) msgs of
        Nothing -> go (ix+1) (c:soFar) cs
        Just (span, msg) ->
          let (here, rest) = splitAt (spanLength span) string
          in
            toSeg soFar ++ Segment here (Just msg) : go (ix + length here) "" rest


plainSegmentSource :: Segment -> String
plainSegmentSource s@(Segment {}) = segmentSource s
plainSegmentSource (SegmentSpace str) = str

hasMessage :: Segment -> Bool
hasMessage s@(Segment {}) = isJust (segmentMessage s)
hasMessage (SegmentSpace {}) = False

plainSource :: Annotated -> String
plainSource (Annotated s) = concatMap plainSegmentSource s

getMessages :: Annotated -> [Maybe Message]
getMessages (Annotated segs) = map go segs
  where
    go (SegmentSpace {}) = Nothing
    go s = segmentMessage s

getExistingMessages :: Annotated -> [Message]
getExistingMessages = catMaybes . getMessages

segmentLength :: Segment -> Int
segmentLength s@(Segment {}) = length (segmentSource s)
segmentLength (SegmentSpace str) = length str

segmentWords :: [(String, Maybe Message)] -> [Segment]
segmentWords xs = intersperse (SegmentSpace " ") (map (uncurry Segment) xs)

sourceMap :: (String -> String) -> Segment -> Segment
sourceMap f seg@(SegmentSpace {}) = seg
sourceMap f (Segment src msg) = Segment (f src) msg

messageLength :: Message -> Int
messageLength = length . messageString

getSpans :: Annotated -> [(SrcSpan, Message)]
getSpans (Annotated segs) = go 0 segs
  where
    go ix [] = []
    go ix (SegmentSpace str:rest) = go (ix+length str) rest
    go ix (Segment src (Just msg):rest) =
      (SrcSpan' ix (length src), msg) : go (ix+length src) rest

    go ix (Segment src Nothing:rest) =
      go (ix+length src) rest

-- example :: Annotated
-- example =
--   Annotated $ segmentWords
--     [ ("source", Just . Message Red $ "Message for " ++ show "source")
--     , ("text", Just . Message Blue $ "Message for " ++ show "text")
--     , ("which", Just . Message Yellow $ "Message for " ++ show "which")
--     , ("goes here", Nothing)
--     ]
--
-- example2 :: Annotated
-- example2 =
--   Annotated $ segmentWords
--     [ ("source", Just . Message Red $ "Message for " ++ show "source")
--     , ("text", Just . Message Blue $ "Message for " ++ show "text")
--     , ("which", Nothing)
--     , ("goes", Just . Message Yellow $ "Message for " ++ show "goes")
--     , ("here", Nothing)
--     ]
--
-- example3 :: Annotated
-- example3 =
--   annotate "source text which goes here"
--     [(Span 0 11, Message Red $ "Message for " ++ show "source text")
--     -- ,(Span 7 4, Message Blue $ "Message for " ++ show "text")
--     -- ,(Span 12 5, Message Yellow $ "Message for " ++ show "which")
--     ,(Span 18 4, Message Yellow $ "Message for " ++ show "goes")
--     ,(Span 23 4, Message Green $ "Message for " ++ show "here")
--     ]
--
