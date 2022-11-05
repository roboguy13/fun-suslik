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
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Void

sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment "--")
  (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

keyword :: String -> Parser String
keyword str = lexeme (string str <* notFollowedBy alphaNumChar)

parseBracketed :: Parser a -> Parser a -> Parser b -> Parser b
parseBracketed left right p = left *> p <* right

parseGuard :: Bool -> Maybe String -> String -> Parser ()
parseGuard True _ _ = pure ()
parseGuard False unexpected expected =
  failure (fmap (Label . NonEmpty.fromList) unexpected) (Set.singleton (Label (NonEmpty.fromList expected)))

parseNameTail :: Parser String
parseNameTail = many (alphaNumChar <|> char '_')

parseUppercaseName :: Parser String
parseUppercaseName = lexeme $ liftA2 (:) upperChar parseNameTail

parseLowercaseName :: Parser String
parseLowercaseName = lexeme $ do
  n <- liftA2 (:) lowerChar parseNameTail
  parseGuard (n `notElem` keywords) (Just n) "identifier"
    -- $ "Expected identifier, found keyword " ++ show n
  pure n
--
--
parseIdentifier :: Parser String
parseIdentifier = label "identifier" $
  parseLowercaseName

keywords :: [String]
keywords = ["lower", "instantiate", "not", "data"]

parseConstructor :: Parser String
parseConstructor = label "constructor name" $
  parseUppercaseName

parseLayoutName :: Parser String
parseLayoutName = label "layout name" $
  parseUppercaseName

parseTypeName :: Parser String
parseTypeName = label "type name" $
  parseUppercaseName
--
parseOp :: String -> Parser String
parseOp str = label str $ symbol str
  -- space *> string str <* space
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
parseList sep p = parseList0 (lexeme sep) p

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
    directives <- some parseDirective

    adts <- some $ lexeme parseAdtDef

    layouts <- some $ lexeme parseLayout

    fns <- some $ lexeme parseFnDef

    -- adts <- parseSpaced parseAdtDef
    -- many parseSpace
    --
    -- layouts <- parseSpaced parseLayout
    -- many parseSpace
    --
    -- fns <- parseSpaced parseFnDef
    pure $ MkParsedFile fns adts layouts directives
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
  GenerateDef
    String   -- | fun-SuSLik function name
    [String] -- | Argument layouts
    String   -- | Result layout
    deriving (Show)

parseDirective :: Parser Directive
parseDirective = parseInstantiateDirective

parseInstantiateDirective :: Parser Directive
parseInstantiateDirective = lexeme $ do
  keyword "%generate"

  fnName <- parseIdentifier

  argLayouts <- parseBracketed (parseOp "[") (parseOp "]")
                  $ parseList (char ',') parseLayoutName

  resultLayout <- parseLayoutName

  pure $ GenerateDef fnName argLayouts resultLayout


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
  keyword "layout"
  parseOp "["
  suslikParams <- parseList (symbol ",") (fmap fsName parseIdentifier)
  parseOp "]"
  parseOp ";"

  -- branches <- parseList (parseOp ";") (go name)
  branches <- some (go name)
  pure $ MkLayout
    { layoutName = name
    , layoutAdtName = tyName
    , layoutSuSLikParams = suslikParams
    , layoutBranches = branches
    }
  where
    go :: String -> Parser (Pattern FsName, Assertion' FsName)
    go name = try $ do
      name' <- parseLayoutName
      parseGuard (name' == name) (Just name') name

      pat <- parsePattern
      parseOp ":="
      rhs <- parseAssertion
      parseOp ";"
      pure (pat, rhs)

parsePattern :: Parser (Pattern FsName)
parsePattern =
  fmap (PatternVar . fsName) parseIdentifier
    <|> do
      parseOp "("
      cName <- parseConstructor
      pVars <- (some (fmap fsName parseIdentifier)) <|> pure []
      parseOp ")"
      pure $ MkPattern cName pVars

parseAssertion :: Parser (Assertion' FsName)
parseAssertion =
  (keyword "emp" *> pure Emp)
    <|>
  parsePointsTo parseAssertion
    <|>
  parseHeapletApply parseAssertion

parsePointsTo :: Parser (Assertion' FsName) -> Parser (Assertion' FsName)
parsePointsTo p = do
  loc <- parseLoc
  parseOp ":->"
  e <- parseExpr
  PointsToI loc e <$> ((parseOp "," *> p) <|> pure Emp)

parseHeapletApply :: Parser (Assertion' FsName) -> Parser (Assertion' FsName)
parseHeapletApply p = do
  layoutName <- parseLayoutName
  -- some spaceChar
  args <- some parseExpr'
  HeapletApply (MkLayoutName (Just Input) layoutName) [] args <$> ((parseOp "," *> p) <|> pure Emp)


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
parseExpr' = lexeme $
  parseBracketed (parseOp "(") (parseOp ")") parseExpr
    <|>
  ((IntLit . read) <$> some digitChar)
    <|>
  (keyword "false" *> pure (BoolLit False))
    <|>
  (keyword "true" *> pure (BoolLit True))
    <|>
  try parseVar

parseExpr :: Parser (Expr FsName)
parseExpr =
  try (Not <$> (keyword "not" *> parseExpr'))
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
  -- some spaceChar
  args <- some parseExpr'
  pure $ Apply f args

parseConstrApp :: Parser (Expr FsName)
parseConstrApp = do
  cName <- parseConstructor
  args <- (some (lexeme parseExpr')) <|> pure []
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
  keyword "lower"

  layoutName <- parseLayoutName

  e <- parseExpr'

  pure $ Lower layoutName e

parseInstantiate :: Parser (Expr FsName)
parseInstantiate = do
  keyword "instantiate"

  layoutA <- parseLayoutName

  layoutB <- parseLayoutName

  e <- parseExpr'

  pure $ LiftLowerFn layoutA layoutB e

parseAdtDef :: Parser Adt
parseAdtDef = do
  -- breakpointM
  keyword "data"

  name <- parseTypeName

  keyword ":="

  branches <- parseList (char '|') parseAdtBranch
  char ';'

  pure $ MkAdt { adtName = name, adtBranches = branches }

parseAdtBranch :: Parser AdtBranch
parseAdtBranch = do
  cName <- parseConstructor
  fields <- (some parseType) <|> pure []
  pure $ MkAdtBranch { adtBranchConstr = cName, adtBranchFields = fields }

parseFnDef :: Parser Def
parseFnDef = do
  name <- parseIdentifier

  parseOp ":"

  ty <- parseType
  parseOp ";"
  -- some newline
  -- many parseSpace

  branches <- some (parseFnBranch name)

  let def = MkDef name ty branches
  -- parseOp ";"

  pure $ def

parseFnBranch :: String -> Parser DefBranch
parseFnBranch name0 = try $ do
  name <- parseIdentifier
  parseGuard (name == name0) (Just name) name0
    -- $ "Expected " ++ show name0 ++ ", found " ++ show name

  -- many spaceChar
  pat <- some parsePattern

  guardeds <- some (parseGuardedExpr)
  -- parseOp ";;"

  -- parseOp ":="
  --
  -- body <- parseExpr

  -- parseOp ";"

  pure $ MkDefBranch pat guardeds

parseGuardedExpr :: Parser GuardedExpr
parseGuardedExpr = lexeme $ do
  cond <- try (parseOp "|" *> parseExpr) <|> pure (BoolLit True)

  parseOp ":="
  body <- parseExpr
  keyword ";"

  pure $ MkGuardedExpr cond body

parseType :: Parser Type
parseType = lexeme $
  try parseFnType
    <|>
  parseBaseType

-- TODO: Parse layout types
parseBaseType :: Parser Type
parseBaseType =
  (keyword "Int" *> pure IntType)
    <|>
  (keyword "Bool" *> pure BoolType)
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
  symbol "->"
  cod <- parseType
  pure $ FnType dom cod
  where
    leftType = parseBaseType <|> parseBracketed (char '(') (char ')') parseType

