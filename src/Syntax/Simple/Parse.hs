{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

-- {-# OPTIONS_GHC -fplugin Debug.Breakpoint #-}

-- {-# OPTIONS_GHC -Wall -Wno-unused-do-bind #-}

module Syntax.Simple.Parse
  where

import           Control.Monad hiding (some, many)
import           Control.Applicative hiding (some, many)

import           Syntax.Simple.Expr
import           Syntax.Simple.Def
import           Syntax.Simple.Heaplet
import           Syntax.Name

import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.List.NonEmpty as NonEmpty

import qualified Data.Set as Set

import           Text.Megaparsec
import           Text.Megaparsec.Char
import           Data.Void

-- import Debug.Trace
-- import GHC.Stack
--
-- import Debug.Breakpoint

-- data ParseLoc = MkParseLoc Int Int
--
-- showParseLoc :: ParseLoc -> String
-- showParseLoc (MkParseLoc r c) =
--   "line " ++ show r ++ ", column " ++ show c
--
-- locNewline :: ParseLoc -> ParseLoc
-- locNewline (MkParseLoc r _) = MkParseLoc (r+1) 1
--
-- locShiftChar :: Char -> ParseLoc -> ParseLoc
-- locShiftChar char loc@(MkParseLoc r c)
--   | char == '\n' || char == '\r' = locNewline loc
--   | otherwise = MkParseLoc r (c+1)
--
-- initialParseLoc :: ParseLoc
-- initialParseLoc = MkParseLoc 1 1
--
-- data ParseValue' a
--   = ParseError [(ParseLoc, String)]
--   | MkParseValue (NonEmpty a)
--   deriving (Functor)
--
--
-- showParseError :: (ParseLoc, String) -> String
-- showParseError (loc, msg) = showParseLoc loc ++ ": " ++ msg
--
-- instance Semigroup (ParseValue' a) where
--   ParseError xs <> ParseError ys = ParseError (xs <> ys)
--
--   x <> (ParseError {}) = x
--   (ParseError {}) <> y = y
--
--   MkParseValue xs <> MkParseValue ys = MkParseValue (xs <> ys)
--
-- instance Monoid (ParseValue' a) where
--   mempty = ParseError [(MkParseLoc 0 0, "Empty parse")]
--
-- instance Applicative ParseValue' where
--   pure = return
--   (<*>) = ap
--
-- instance Monad ParseValue' where
--   return x = MkParseValue (x :| [])
--   ParseError e >>= _ = ParseError e
--   MkParseValue xs >>= f = foldMap f xs
--   -- MkParseValue (x :| xs) >>= f =
--   --   let z = last (x : xs)
--   --   in
--   --   foldr ((<>) . f) (f z) (init (x:xs))
--
-- -- instance Alternative ParseValue' where
-- --   empty = mempty
-- --   (<|>) = (<>)
--
--
-- type ParseValue a = ParseValue' (ParseLoc, String, a)
--
-- oneParseValue :: ParseLoc -> String -> a -> ParseValue a
-- oneParseValue loc rest x = MkParseValue ((loc, rest, x) :| [])
--
-- newtype Parser a = MkParser { runParser :: (ParseLoc, String) -> ParseValue a }
--   deriving (Functor)
--
-- parseError :: String -> Parser a
-- parseError msg = MkParser $ \(loc, _) -> ParseError [(loc, msg)]
--
-- parseGuard :: Bool -> String -> Parser ()
-- parseGuard True _ = pure ()
-- parseGuard False msg = parseError msg
--
-- parse :: Parser a -> String -> Either String a
-- parse p str =
--   case runParser (p <* parseEOF) (initialParseLoc, str) of
--   -- case runParser p (initialParseLoc, str) of
--     -- ParseError e -> Left $ unlines $ map showParseError e
--     ParseError e -> Left $ showParseError (head e)
--     MkParseValue ((_, "", x) :| _) -> Right x
--     MkParseValue ((_, rest, _) :| _) ->
--       Left $ "Couldn't finish parsing: rest of file: \n" ++ truncateString rest 500 ++ "\n"
--   where
--     truncateString "" 0 = ""
--     truncateString _ 0 = "\n..."
--     truncateString "" _ = ""
--     truncateString (c:cs) n = c : truncateString cs (n-1)
--   -- case NonEmpty.filter (null . fst) (runParser p str) of
--   --   ParseError e -> Left e
--   --   MkParseValue ((_,x) : _) -> Just x
--   --   MkParseValue [] -> Just "Empty parse"
--
-- parse' :: Parser a -> String -> a
-- parse' p str =
--   case parse p str of
--     Left e -> error $ "Parse error: " ++ e
--     Right x -> x
--
-- withExpected :: String -> Parser a -> Parser a
-- withExpected msg p =
--   MkParser $ \(loc, s) ->
--     case runParser p (loc, s) of
--       ParseError es -> ParseError ((loc, "Expected " ++ msg):es)
--       MkParseValue x -> MkParseValue x
--
-- instance Applicative Parser where
--   pure = return
--   (<*>) = ap
--
-- instance Monad Parser where
--   return x = MkParser (\(loc, s) -> oneParseValue loc s x)
--   MkParser p >>= f =
--     MkParser $ \arg -> do
--       (loc, s', x) <- p arg
--       runParser (f x) (loc, s')
--
-- instance Alternative Parser where
--   empty = MkParser $ \(loc, _) -> ParseError [(loc, "Empty parse")]
--   (<|>) = (<|>)
--
-- (<|>) :: Parser a -> Parser a -> Parser a
-- p <|> q =
--   MkParser (\s -> runParser p s <> runParser q s)
--
-- some :: Parser a -> Parser [a]
-- some = some
-- -- some p =
-- --   MkParser $ \(loc, s) ->
-- --     case runParser p (loc, s) of
-- --       ParseError e -> ParseError e
-- --       r -> runParser (some p) (loc, s)
-- --   -- where
-- --   --   goMany = goSome <|> pure []
-- --   --   goSome = liftA2 (:) p goMany
--
-- many :: Parser a -> Parser [a]
-- many = many
--   -- where
--   --   goMany = goSome <|> pure []
--   --   goSome = liftA2 (:) p goMany
--
-- parseCharWhen :: (Char -> Bool) -> Parser Char
-- parseCharWhen pred = MkParser $ \case
--   (loc, "") -> ParseError [(MkParseLoc 0 0, "Empty parse")]
--   (loc, c:cs)
--     | pred c    -> pure (locShiftChar c loc, cs, c)
--     | otherwise ->
--         ParseError [(loc, "Unexpected " ++ show c)]
--
-- parseChar :: Char -> Parser Char
-- parseChar c =
--   withExpected (show c) $ parseCharWhen (== c)
--
-- parseString :: HasCallStack => String -> Parser String
-- parseString str = withExpected (show str) $ MkParser $ \(loc, curr) ->
--   breakpoint $
--   runParser (mapM parseChar str) (loc, curr)
--
-- parseOneOf :: [Char] -> Parser Char
-- parseOneOf cs = withExpected ("one of " ++ show cs) $
--   parseCharWhen (`elem` cs)
--
-- parseNewline :: Parser Char
-- parseNewline = withExpected "newline" $
--   parseOneOf "\n\r"
--
-- parseEOF :: Parser ()
-- parseEOF = MkParser $ \(loc, str) ->
--   case str of
--     "" -> MkParseValue ((MkParseLoc 0 0, "", ()) :| [])
--     (c:_) -> ParseError [(loc, "Expected end-of-file, found " ++ show c)]
--
-- parseSpace :: Parser Char
-- parseSpace = withExpected "space" $
--   parseOneOf "\t\n\r "
--
parseBracketed :: Parser a -> Parser a -> Parser b -> Parser b
parseBracketed left right p = left *> p <* right

--
-- parseList0 :: Parser a -> Parser b -> Parser [b]
-- parseList0 sep p = go
--   where
--     go =
--       liftA2 (:) p (sep *> go)
--         <|>
--       fmap (:[]) p
--
-- parseList :: Parser a -> Parser b -> Parser [b]
-- parseList sep p = parseList0 (many parseSpace *> sep <* many parseSpace) p
--
-- parseSpaced :: Parser b -> Parser [b]
-- parseSpaced = parseList0 (some parseSpace)
--
-- parseAlpha :: Parser Char
-- parseAlpha = parseOneOf cs
--   where
--     cs = ['a'..'z'] ++ ['A'..'Z']
--
-- parseLowercase :: Parser Char
-- parseLowercase = parseOneOf ['a'..'z']
--
-- parseUppercase :: Parser Char
-- parseUppercase = parseOneOf ['A'..'Z']
--
-- parseDigit :: Parser Char
-- parseDigit = withExpected "digit" $
--   parseOneOf ['0'..'9']
--
-- parseAlphanum :: Parser Char
-- parseAlphanum = parseAlpha <|> parseDigit
--

withExpected = label

parseGuard :: Bool -> Maybe String -> String -> Parser ()
parseGuard True _ _ = pure ()
parseGuard False unexpected expected =
  failure (fmap (Label . NonEmpty.fromList) unexpected) (Set.singleton (Label (NonEmpty.fromList expected)))

parseNameTail :: Parser String
parseNameTail = many (alphaNumChar <|> char '_')

parseUppercaseName :: Parser String
parseUppercaseName = liftA2 (:) upperChar parseNameTail

parseLowercaseName :: Parser String
parseLowercaseName = do
  n <- liftA2 (:) lowerChar parseNameTail
  parseGuard (n `notElem` keywords) (Just n) "identifier"
    -- $ "Expected identifier, found keyword " ++ show n
  pure n
--
--
parseIdentifier :: Parser String
parseIdentifier = withExpected "identifier" $
  parseLowercaseName

keywords :: [String]
keywords = ["lower", "instantiate", "not", "data"]


parseConstructor :: Parser String
parseConstructor = withExpected "constructor name" $
  parseUppercaseName

parseLayoutName :: Parser String
parseLayoutName = withExpected "layout name" $
  parseUppercaseName

parseTypeName :: Parser String
parseTypeName = withExpected "type name" $
  parseUppercaseName
--
parseOp :: String -> Parser String
parseOp str = withExpected str $
  space *> string str <* space
--
-- optionalParse :: a -> Parser a -> Parser a
-- optionalParse def p = p <|> pure def
--
-- atLineStart :: Parser ()
-- atLineStart = MkParser $ \(loc@(MkParseLoc _ c), rest) ->
--   if c /= 1
--     then ParseError [(loc, "Expected to be at start of line")]
--     else MkParseValue ((loc, rest, ()) :| [])
--   -- parseGuard (c == 1) "Expected to be at start of line"

type Parser = Parsec Void String

parse' :: Parser a -> String -> a
parse' p str =
  case parse p "<input>" str of
    Left err -> error $ errorBundlePretty err
    Right x -> x

parseSpaced :: Parser a -> Parser [a]
parseSpaced p = sepBy1 p spaceChar

parseList0 :: Parser a -> Parser b -> Parser [b]
parseList0 sep p = sepBy p sep

parseList :: Parser a -> Parser b -> Parser [b]
parseList sep p = parseList0 (many spaceChar *> sep <* many spaceChar) p

-------

data ParsedFile =
  MkParsedFile
  { fileFnDefs :: [Def]
  , fileAdts :: [Adt]
  , fileLayouts :: [Layout]
  , fileDirectives :: [Directive]
  }
  deriving (Show)

instance Semigroup ParsedFile where
  MkParsedFile x y z w <> MkParsedFile x' y' z' w' =
    MkParsedFile (x <> x') (y <> y') (z <> z') (w <> w')

instance Monoid ParsedFile where
  mempty = MkParsedFile [] [] [] []

oneFileFnDef :: Def -> ParsedFile
oneFileFnDef d = MkParsedFile [d] [] [] []

oneFileAdt :: Adt -> ParsedFile
oneFileAdt adt = MkParsedFile [] [adt] [] []

oneFileLayout :: Layout -> ParsedFile
oneFileLayout layout = MkParsedFile [] [] [layout] []

oneFileDirective :: Directive -> ParsedFile
oneFileDirective d = MkParsedFile [] [] [] [d]

parseFile :: Parser ParsedFile
parseFile = do
    directive <- parseDirective
    some newline

    adts <- parseSpaced parseAdtDef
    some newline

    layouts <- parseSpaced parseLayout
    some newline

    fns <- parseSpaced parseFnDef
    many spaceChar

    -- adts <- parseSpaced parseAdtDef
    -- many parseSpace
    --
    -- layouts <- parseSpaced parseLayout
    -- many parseSpace
    --
    -- fns <- parseSpaced parseFnDef
    pure $ MkParsedFile fns adts layouts [directive]
  --   some parseSpace
  --   body <- mconcat <$> some (many parseSpace *> go)
  --
  --   pure (oneFileDirective directive <> body)
  -- where
  --   go =
  --     (oneFileFnDef <$> parseFnDef)
  --       <|>
  --     (oneFileAdt <$> parseAdtDef)
  --       <|>
  --     (oneFileLayout <$> parseLayout)

data Directive =
  InstantiateDef
    String   -- | fun-SuSLik function name
    [String] -- | Argument layouts
    String   -- | Result layout
    deriving (Show)

parseDirective :: Parser Directive
parseDirective = parseInstantiateDirective

parseInstantiateDirective :: Parser Directive
parseInstantiateDirective = do
  string "%instantiate"
  some spaceChar

  fnName <- parseIdentifier
  some spaceChar

  argLayouts <- parseBracketed (parseOp "[") (parseOp "]")
                  $ parseList (char ',') parseLayoutName
  some spaceChar

  resultLayout <- parseLayoutName

  pure $ InstantiateDef fnName argLayouts resultLayout


data GlobalItem where
  -- GlobalAdt :: Adt -> GlobalItem
  GlobalLayout :: Layout -> GlobalItem
  GlobalFnDef :: Def -> GlobalItem
  deriving (Show)

type GlobalEnv = [(String, GlobalItem)]

parseLayout :: Parser Layout
parseLayout = do
  name <- parseLayoutName
  parseOp ":"
  tyName <- parseTypeName
  parseOp ">->"
  string "layout"
  parseOp "["
  suslikParams <- parseList (char ',') (fmap fsName parseIdentifier)
  parseOp "]"
  -- parseOp ";"
  newline
  many spaceChar

  -- branches <- parseList (parseOp ";") (go name)
  branches <- some (go name)
  parseOp ";"
  pure $ MkLayout
    { layoutName = name
    , layoutAdtName = tyName
    , layoutSuSLikParams = suslikParams
    , layoutBranches = branches
    }
  where
    go :: String -> Parser (Pattern FsName, Assertion' FsName)
    go name = do
      name' <- parseLayoutName
      parseGuard (name' == name) (Just name) name'
      some spaceChar

      pat <- parsePattern
      parseOp ":="
      rhs <- parseAssertion
      -- parseOp ";"
      many newline
      pure (pat, rhs)

parsePattern :: Parser (Pattern FsName)
parsePattern =
  fmap (PatternVar . fsName) parseIdentifier
    <|> do
      parseOp "("
      cName <- parseConstructor
      pVars <- (some spaceChar *> parseSpaced (fmap fsName parseIdentifier)) <|> pure []
      parseOp ")"
      pure $ MkPattern cName pVars

parseAssertion :: Parser (Assertion' FsName)
parseAssertion =
  (string "emp" *> pure Emp)
    <|>
  parsePointsTo parseAssertion
    <|>
  parseHeapletApply parseAssertion

parsePointsTo :: Parser (Assertion' FsName) -> Parser (Assertion' FsName)
parsePointsTo p = do
  loc <- parseLoc
  parseOp ":->"
  e <- parseExpr
  PointsTo loc e <$> ((parseOp "," *> p) <|> pure Emp)

parseHeapletApply :: Parser (Assertion' FsName) -> Parser (Assertion' FsName)
parseHeapletApply p = do
  layoutName <- parseLayoutName
  some spaceChar
  args <- parseSpaced parseExpr
  HeapletApply layoutName [] args <$> ((parseOp "," *> p) <|> pure Emp)


parseLoc :: Parser (Loc (Expr FsName))
parseLoc = fmap (Here . Var . fsName) parseIdentifier <|> go
  where
    go = do
      parseOp "("
      x <- parseIdentifier
      parseOp "+"
      i <- read @Int <$> some digitChar
      parseOp ")"
      pure (Var (fsName x) :+ i)

parseExpr' :: Parser (Expr FsName)
parseExpr' =
  parseBracketed (parseOp "(") (parseOp ")") parseExpr
    <|>
  ((IntLit . read) <$> some digitChar)
    <|>
  (string "false" *> pure (BoolLit False))
    <|>
  (string "true" *> pure (BoolLit True))
    <|>
  try parseVar

parseExpr :: Parser (Expr FsName)
parseExpr =
  try (Not <$> (string "not" *> some spaceChar *> parseExpr'))
    <|>
  parseBinOp "&&" And
    <|>
  parseBinOp "||" Or
    <|>
  parseBinOp "+" Add
    <|>
  parseBinOp "-" Sub
    <|>
  parseBinOp "*" Mul
    <|>
  parseBinOp "==" Equal
    <|>
  parseBinOp "<=" Le
    <|>
  parseBinOp "<" Lt
    <|>
  try parseLower
    <|>
  try parseInstantiate
    <|>
  try parseApp
    <|>
  try parseConstrApp
    <|>
  try parseExpr'

parseApp :: Parser (Expr FsName)
parseApp = do
  f <- parseIdentifier
  some spaceChar
  args <- parseSpaced parseExpr'
  pure $ Apply f args

parseConstrApp :: Parser (Expr FsName)
parseConstrApp = do
  cName <- parseConstructor
  args <- (some spaceChar *> parseSpaced parseExpr') <|> pure []
  pure $ ConstrApply cName args

parseBinOp :: String -> (Expr FsName -> Expr FsName -> Expr FsName) -> Parser (Expr FsName)
parseBinOp opName build = try $ do
  x <- try parseExpr'
  parseOp opName
  y <- parseExpr
  pure $ build x y

parseVar :: Parser (Expr FsName)
parseVar = do
  str <- parseIdentifier
  pure $ Var (fsName str)

parseLower :: Parser (Expr FsName)
parseLower = do
  string "lower"

  some spaceChar
  layoutName <- parseLayoutName

  some spaceChar
  e <- parseExpr'

  pure $ Lower layoutName [] e

parseInstantiate :: Parser (Expr FsName)
parseInstantiate = do
  string "instantiate"

  some spaceChar
  layoutA <- parseLayoutName

  some spaceChar
  layoutB <- parseLayoutName

  some spaceChar
  e <- parseExpr'

  pure $ LiftLowerFn layoutA layoutB e

parseAdtDef :: Parser Adt
parseAdtDef = do
  -- breakpointM
  string "data"

  some spaceChar
  name <- parseTypeName

  many spaceChar
  string ":="

  many spaceChar
  branches <- parseList (char '|') parseAdtBranch
  char ';'

  pure $ MkAdt { adtName = name, adtBranches = branches }

parseAdtBranch :: Parser AdtBranch
parseAdtBranch = do
  cName <- parseConstructor
  fields <- (some spaceChar *> parseSpaced parseType) <|> pure []
  pure $ MkAdtBranch { adtBranchConstr = cName, adtBranchFields = fields }

parseFnDef :: Parser Def
parseFnDef = do
  name <- parseIdentifier

  parseOp ":"

  ty <- parseType
  -- parseOp ";"
  some newline
  -- many parseSpace

  branches <- parseSpaced (try $ parseFnBranch name)

  let def = MkDef name ty branches
  -- parseOp ";"

  pure $ def

parseFnBranch :: String -> Parser DefBranch
parseFnBranch name0 = do
  name <- try parseIdentifier
  parseGuard (name == name0) (Just name) name0
    -- $ "Expected " ++ show name0 ++ ", found " ++ show name

  many spaceChar
  pat <- parseSpaced parsePattern

  guardeds <- parseSpaced (try parseGuardedExpr)
  -- parseOp ";;"

  -- parseOp ":="
  --
  -- body <- parseExpr

  -- parseOp ";"

  pure $ MkDefBranch pat guardeds

parseGuardedExpr :: Parser GuardedExpr
parseGuardedExpr = do
  cond <- try (parseOp "|" *> parseExpr) <|> pure (BoolLit True)

  parseOp ":="
  body <- parseExpr
  string ";"

  pure $ MkGuardedExpr cond body

parseType :: Parser Type
parseType =
  try parseFnType
    <|>
  parseBaseType

-- TODO: Parse layout types
parseBaseType :: Parser Type
parseBaseType =
  (string "Int" *> pure IntType)
    <|>
  (string "Bool" *> pure BoolType)
    <|>
  (fmap AdtType go)
  where
    go = do
      str <- parseTypeName
      parseGuard (str `notElem` reservedTypes) (Just str) "non-reserved type name"
        -- $ "Expected non-reserved type name, found " ++ show str
      pure str

    reservedTypes = ["Int", "Bool"]

parseFnType :: Parser Type
parseFnType = do
  dom <- leftType
  some spaceChar
  chunk "->"
  some spaceChar
  cod <- parseType
  pure $ FnType dom cod
  where
    leftType = parseBaseType <|> parseBracketed (char '(') (char ')') parseType

