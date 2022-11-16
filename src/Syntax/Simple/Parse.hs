{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

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
keywords = ["lower", "instantiate", "not", "data", "deref", "addr", "in", "let", "if", "then", "else"]

parseConstructor :: Parser String
parseConstructor = label "constructor name" $
  parseUppercaseName

parseMode :: Parser Mode
parseMode = label "mode" $
  (keyword "readonly" *> pure Input) <|>
  (keyword "mutable" *> pure Output)

parseSimpleLayoutName :: Parser String
parseSimpleLayoutName = label "layout name" $
  parseUppercaseName

parseLayoutName :: Parser LayoutName
parseLayoutName = label "moded layout name" $ do
  name <- parseSimpleLayoutName
  parseOp "["
  mode <- parseMode
  parseOp "]"
  pure $ MkLayoutName (Just mode) name

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
  { fileFnDefs :: [ParsedDef]
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

oneFileFnDef :: ParsedDef -> ParsedFile
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
    [ParamType] -- | Argument layouts
    ParamType   -- | Result layout
    deriving (Show)

parseDirective :: Parser Directive
parseDirective = parseInstantiateDirective

parseInstantiateDirective :: Parser Directive
parseInstantiateDirective = lexeme $ do
  keyword "%generate"

  fnName <- parseIdentifier

  argLayouts <- parseBracketed (parseOp "[") (parseOp "]")
                  $ parseList (char ',') parseParamType

  resultLayout <- parseSimpleParamType

  pure $ GenerateDef fnName argLayouts resultLayout


data GlobalItem where
  -- GlobalAdt :: Adt -> GlobalItem
  GlobalLayout :: Layout -> GlobalItem
  GlobalFnDef :: ParsedDef -> GlobalItem
  deriving (Show)

type GlobalEnv = [(String, GlobalItem)]

parseLayout :: Parser Layout
parseLayout = do
  name <- parseSimpleLayoutName
  parseOp ":"
  tyName <- parseTypeName
  parseOp ">->"
  keyword "layout"
  parseOp "["
  suslikParams <- parseList (symbol ",") parseIdentifier
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
    go :: String -> Parser (Pattern, Assertion FsName)
    go name = try $ do
      name' <- parseSimpleLayoutName
      parseGuard (name' == name) (Just name') name

      pat <- parsePattern
      parseOp ":="
      rhs <- parseAssertion
      parseOp ";"
      pure (pat, rhs)

parsePattern :: Parser Pattern
parsePattern =
  fmap (PatternVar () . fsName) parseIdentifier
    <|> do
      parseOp "("
      cName <- parseConstructor
      pVars <- (some (fmap fsName parseIdentifier)) <|> pure []
      parseOp ")"
      pure $ MkPattern () cName pVars

parseAssertion :: Parser (Assertion FsName)
parseAssertion =
  (keyword "emp" *> pure Emp)
    <|>
  parsePointsTo parseAssertion
    <|>
  parseHeapletApply parseAssertion

parsePointsTo :: Parser (Assertion FsName) -> Parser (Assertion FsName)
parsePointsTo p = do
  loc <- parseLoc
  parseOp ":->"
  e <- parseSuSLikExpr'
  -- e <- fmap (Var ()) parseIdentifier
  PointsToI loc e <$> ((parseOp "," *> p) <|> pure Emp)

parseHeapletApply :: Parser (Assertion FsName) -> Parser (Assertion FsName)
parseHeapletApply p = do
  layoutName <- parseSimpleLayoutName
  -- some spaceChar
  -- args <- some parseExpr'
  argId <- parseIdentifier
  let arg = Var () argId
  let args = [arg]
  HeapletApply (MkLayoutName (Just Input) layoutName) [VarS argId] args <$> ((parseOp "," *> p) <|> pure Emp)
  -- HeapletApply (MkLayoutName (Just Input) layoutName) [] args <$> ((parseOp "," *> p) <|> pure Emp)


parseLoc :: Parser (Loc FsName)
parseLoc = fmap (Here . fsName) parseIdentifier <|> go
  where
    go = do
      parseOp "("
      x <- parseIdentifier
      parseOp "+"
      i <- read @Int <$> some digitChar
      parseOp ")"
      pure ((fsName x) :+ i)

parseSuSLikExpr' :: Parser (SuSLikExpr SuSLikName)
parseSuSLikExpr' = lexeme $
  parseBracketed (parseOp "(") (parseOp ")") parseSuSLikExpr <|>
  ((IntS . read) <$> some digitChar) <|>
  (keyword "false" *> pure (BoolS False)) <|>
  (keyword "true" *> pure (BoolS True)) <|>
  (VarS <$> parseIdentifier)

parseSuSLikExpr :: Parser (SuSLikExpr FsName)
parseSuSLikExpr =
  try (NotS <$> (keyword "not" *> parseSuSLikExpr'))
    <|>
  parseSuSLikBinOp "&&" AndS
    <|>
  parseSuSLikBinOp "||" OrS
    <|>
  parseSuSLikBinOp "+" AddS
    <|>
  parseSuSLikBinOp "-" SubS
    <|>
  parseSuSLikBinOp "*" MulS
    <|>
  parseSuSLikBinOp "==" EqualS
    <|>
  parseSuSLikBinOp "<=" LeS
    <|>
  parseSuSLikBinOp "<" LtS

parseExpr' :: Parser (Parsed ExprX FsName)
parseExpr' = lexeme $
  parseBracketed (parseOp "(") (parseOp ")") parseExpr
    <|>
  ((IntLit . read) <$> some digitChar)
    <|>
  (keyword "false" *> pure (BoolLit False))
    <|>
  (keyword "true" *> pure (BoolLit True))
    <|>
  try parseLetIn
    <|>
  try parseIfThenElse
    <|>
  try parseVar

parseExpr :: Parser (Parsed ExprX FsName)
parseExpr =
  try (Not <$> (keyword "not" *> parseExpr'))
    <|>
  try (Deref () <$> (keyword "deref" *> parseExpr'))
    <|>
  try (Addr () <$> (keyword "addr" *> parseExpr'))
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

parseApp :: Parser (Parsed ExprX FsName)
parseApp = do
  f <- parseIdentifier
  -- some spaceChar
  args <- some parseExpr'
  pure $ Apply f () (replicate (length args) ()) args

parseConstrApp :: Parser (Parsed ExprX FsName)
parseConstrApp = do
  cName <- parseConstructor
  args <- (some (lexeme parseExpr')) <|> pure []
  pure $ ConstrApply () cName args

parseBinOp :: String -> (Parsed ExprX FsName -> Parsed ExprX FsName -> Parsed ExprX FsName) -> Parser (Parsed ExprX FsName)
parseBinOp opName build = try $ do
  x <- try parseExpr'
  parseOp opName
  y <- parseExpr
  pure $ build x y

parseSuSLikBinOp :: String -> (SuSLikExpr FsName -> SuSLikExpr FsName -> SuSLikExpr FsName) -> Parser (SuSLikExpr FsName)
parseSuSLikBinOp opName build = try $ do
  x <- try parseSuSLikExpr'
  parseOp opName
  y <- parseSuSLikExpr
  pure $ build x y

parseVar :: Parser (Parsed ExprX FsName)
parseVar = do
  str <- parseIdentifier
  pure $ Var () (fsName str)

parseParamType0 :: Parser LayoutName -> Parser ParamType
parseParamType0 p =
  try (parseBracketed (parseOp "(") (parseOp ")") (parseParamType0 p)) <|>
  try (keyword "Int" *> pure (IntParam Nothing)) <|>
  try (keyword "Bool" *> pure (BoolParam Nothing)) <|>
  try (PtrParam Nothing <$> parsePtrType) <|>
  try (fmap LayoutParam p)

parseParamType :: Parser ParamType
parseParamType = parseParamType0 parseLayoutName

parseSimpleParamType :: Parser ParamType
parseSimpleParamType =
  parseParamType0 (fmap (MkLayoutName (Just Output)) parseSimpleLayoutName)

parseLetIn :: Parser (Parsed ExprX FsName)
parseLetIn = lexeme $ do
  keyword "let"
  v <- parseIdentifier

  parseOp ":="

  rhs <- parseExpr

  keyword "in"

  body <- parseExpr

  pure $ LetIn () v rhs body

parseIfThenElse :: Parser (Parsed ExprX FsName)
parseIfThenElse = lexeme $ do
  keyword "if"

  c <- parseExpr

  keyword "then"

  t <- parseExpr

  keyword "else"

  f <- parseExpr

  pure $ IfThenElse () c t f

parseLower :: Parser (Parsed ExprX FsName)
parseLower = lexeme $ do
  keyword "lower"

  layoutName <- parseParamType

  e <- parseExpr'

  pure $ Lower layoutName e

parseInstantiate :: Parser (Parsed ExprX FsName)
parseInstantiate = lexeme $ do
  keyword "instantiate"

  argLayouts <- parseBracketed (parseOp "[") (parseOp "]")
                  $ parseList (char ',') parseParamType

  resultLayout <- parseSimpleParamType

  f <- parseIdentifier

  args <- some parseExpr'

  when (length args /= length argLayouts)
    $ failure (Just (Label (NonEmpty.fromList (show (length args) ++ " arguments, " ++ show (length argLayouts) ++ " argument layouts"))))
              (Set.singleton (Label (NonEmpty.fromList ("Same number of arguments and argument layouts"))))

  pure $ Instantiate argLayouts resultLayout f args

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

parseFnDef :: Parser ParsedDef
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

parseFnBranch :: String -> Parser (ParsedDefBranch)
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

parseGuardedExpr :: Parser (Parsed GuardedExpr)
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
  parseUnnestedType

parseBaseType :: Parser BaseType
parseBaseType =
  (keyword "Int" *> pure IntBase)
    <|>
  (keyword "Bool" *> pure BoolBase)

parsePtrType :: Parser BaseType
parsePtrType =
  keyword "Ptr" *> parseBaseType


-- TODO: Parse layout types
parseUnnestedType :: Parser Type
parseUnnestedType =
  fmap baseToType parseBaseType
    <|>
  fmap PtrType parsePtrType
    <|>
  (fmap AdtType go)
  where
    go = do
      str <- parseTypeName
      parseGuard (str `notElem` reservedTypes) (Just str) "non-reserved type name"
        -- $ "Expected non-reserved type name, found " ++ show str
      pure str

    reservedTypes = ["Int", "Bool", "Ptr"]

parseFnType :: Parser Type
parseFnType = do
  dom <- leftType
  symbol "->"
  cod <- parseType
  pure $ FnType dom cod
  where
    leftType = parseUnnestedType <|> parseBracketed (char '(') (char ')') parseType

