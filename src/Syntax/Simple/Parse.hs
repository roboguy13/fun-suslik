{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module Syntax.Simple.Parse
  where

import           Control.Monad
import           Control.Applicative

import           Syntax.Simple.Expr
import           Syntax.Simple.Def
import           Syntax.Simple.Heaplet
import           Syntax.Name

newtype Parser a = MkParser { runParser :: String -> [(String, a)] }
  deriving (Functor)

parse :: Parser a -> String -> Maybe a
parse p str =
  case filter (null . fst) (runParser p str) of
    [] -> Nothing
    ((_,x):_) -> Just x

parse' :: Parser a -> String -> a
parse' p str =
  case parse p str of
    Nothing -> error "Parse error"
    Just x -> x

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Monad Parser where
  return x = MkParser (\s -> [(s, x)])
  MkParser p >>= f =
    MkParser $ \s -> do
      (s', x) <- p s
      runParser (f x) s'

instance Alternative Parser where
  empty = MkParser $ const mempty
  p <|> q =
    MkParser (\s -> runParser p s <|> runParser q s)

parseCharWhen :: (Char -> Bool) -> Parser Char
parseCharWhen pred = MkParser $ \case
  "" -> empty
  (c:cs)
    | pred c    -> pure (cs, c)
    | otherwise -> empty

parseChar :: Char -> Parser Char
parseChar c = parseCharWhen (== c)

parseString :: String -> Parser String
parseString = mapM parseChar

parseOneOf :: [Char] -> Parser Char
parseOneOf cs = parseCharWhen (`elem` cs)

parseSpace :: Parser Char
parseSpace = parseOneOf "\t\n\r "

parseBracketed :: Parser a -> Parser a -> Parser b -> Parser b
parseBracketed left right p = left *> p <* right

parseList0 :: Parser a -> Parser b -> Parser [b]
parseList0 sep p = go
  where
    go =
      fmap (:[]) p
        <|>
      liftA2 (:) p (sep *> go)

parseList :: Parser a -> Parser b -> Parser [b]
parseList sep p = parseList0 (many parseSpace *> sep <* many parseSpace) p

parseSpaced :: Parser b -> Parser [b]
parseSpaced = parseList0 (some parseSpace)

parseAlpha :: Parser Char
parseAlpha = parseOneOf cs
  where
    cs = ['a'..'z'] ++ ['A'..'Z']

parseLowercase :: Parser Char
parseLowercase = parseOneOf ['a'..'z']

parseUppercase :: Parser Char
parseUppercase = parseOneOf ['A'..'Z']

parseDigit :: Parser Char
parseDigit = parseOneOf ['0'..'9']

parseAlphanum :: Parser Char
parseAlphanum = parseAlpha <|> parseDigit

parseNameTail :: Parser String
parseNameTail = many (parseAlphanum <|> parseChar '_')

parseUppercaseName :: Parser String
parseUppercaseName = liftA2 (:) parseUppercase parseNameTail

parseLowercaseName :: Parser String
parseLowercaseName = liftA2 (:) parseLowercase parseNameTail

parseIdentifier :: Parser String
parseIdentifier = parseLowercaseName

parseConstructor :: Parser String
parseConstructor = parseUppercaseName

parseLayoutName :: Parser String
parseLayoutName = parseUppercaseName

parseTypeName :: Parser String
parseTypeName = parseUppercaseName

parseOp :: String -> Parser String
parseOp str = many parseSpace *> parseString str <* many parseSpace

optionalParse :: a -> Parser a -> Parser a
optionalParse def p = p <|> pure def

-------

-- data ParsedType where
--   PIntType :: ParsedType
--   PBoolType :: ParsedType
--   PFnType :: ParsedType -> ParsedType -> ParsedType
--   PTypeName :: String -> ParsedType
--   deriving (Show)

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
  parseString "layout"
  parseOp "["
  suslikParams <- parseList (parseChar ',') (fmap fsName parseIdentifier)
  parseOp "]"
  parseOp ";"

  branches <- parseList (parseChar ';') (go name)
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
      guard (name' == name)
      pat <- parsePattern
      parseOp ":="
      rhs <- parseAssertion
      pure (pat, rhs)

parsePattern :: Parser (Pattern FsName)
parsePattern = do
  parseOp "("
  cName <- parseConstructor
  pVars <- (some parseSpace *> parseSpaced (fmap fsName parseIdentifier)) <|> pure []
  parseOp ")"
  pure $ MkPattern cName pVars

parseAssertion :: Parser (Assertion' FsName)
parseAssertion =
  (parseString "emp" *> pure Emp)
    <|>
  parsePointsTo parseAssertion
    <|>
  parseHeapletApply parseAssertion

parsePointsTo :: Parser (Assertion' FsName) -> Parser (Assertion' FsName)
parsePointsTo p = do
  loc <- parseLoc
  parseOp ":->"
  e <- parseExpr
  PointsTo loc e <$> (optionalParse Emp (parseOp "," *> p))

parseHeapletApply :: Parser (Assertion' FsName) -> Parser (Assertion' FsName)
parseHeapletApply p = do
  layoutName <- parseLayoutName
  some parseSpace
  arg <- parseExpr
  HeapletApply layoutName [] arg <$> (optionalParse Emp (parseOp "," *> p))


parseLoc :: Parser (Loc (Expr FsName))
parseLoc = fmap (Here . Var . fsName) parseIdentifier <|> go
  where
    go = do
      parseOp "("
      x <- parseIdentifier
      parseOp "+"
      i <- read @Int <$> some parseDigit
      parseOp ")"
      pure (Var (fsName x) :+ i)

parseExpr' :: Parser (Expr FsName)
parseExpr' =
  parseBracketed (parseOp "(") (parseOp ")") parseExpr
    <|>
  ((IntLit . read) <$> some parseDigit)
    <|>
  (parseString "false" *> pure (BoolLit False))
    <|>
  (parseString "true" *> pure (BoolLit True))
    <|>
  parseVar

parseExpr :: Parser (Expr FsName)
parseExpr =
  parseExpr'
    <|>
  (Not <$> (parseString "not" *> some parseSpace *> parseExpr'))
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
  parseLower
    <|>
  parseInstantiate
    <|>
  parseApp
    <|>
  parseConstrApp

parseApp :: Parser (Expr FsName)
parseApp = do
  f <- parseIdentifier
  some parseSpace
  arg <- parseExpr'
  pure $ Apply f arg

parseConstrApp :: Parser (Expr FsName)
parseConstrApp = do
  cName <- parseConstructor
  args <- (some parseSpace *> parseSpaced parseExpr') <|> pure []
  pure $ ConstrApply cName args

parseBinOp :: String -> (Expr FsName -> Expr FsName -> Expr FsName) -> Parser (Expr FsName)
parseBinOp opName build = do
  x <- parseExpr'
  parseOp opName
  y <- parseExpr
  pure $ build x y

parseVar :: Parser (Expr FsName)
parseVar = do
  str <- parseIdentifier
  guard (str `notElem` keywords)
  pure $ Var (fsName str)
  where
    keywords = ["lower", "instantiate", "not"]

parseLower :: Parser (Expr FsName)
parseLower = do
  parseString "lower"

  some parseSpace
  layoutName <- parseLayoutName

  some parseSpace
  e <- parseExpr'

  pure $ Lower layoutName [] e

parseInstantiate :: Parser (Expr FsName)
parseInstantiate = do
  parseString "instantiate"

  some parseSpace
  layoutA <- parseLayoutName

  some parseSpace
  layoutB <- parseLayoutName

  some parseSpace
  e <- parseExpr'

  pure $ LiftLowerFn layoutA layoutB e

parseAdtDef :: Parser Adt
parseAdtDef = do
  parseString "data"

  some parseSpace
  name <- parseTypeName

  many parseSpace
  parseString ":="

  many parseSpace
  branches <- parseList (parseChar '|') parseAdtBranch
  parseChar ';'

  pure $ MkAdt { adtName = name, adtBranches = branches }

parseAdtBranch :: Parser AdtBranch
parseAdtBranch = do
  cName <- parseConstructor
  fields <- optionalParse [] (some parseSpace *> parseSpaced parseType)
  pure $ MkAdtBranch { adtBranchConstr = cName, adtBranchFields = fields }

parseFnDef :: Parser Def
parseFnDef = do
  name <- parseIdentifier

  parseOp ":"

  ty <- parseType
  parseOp ";"

  branches <- some (parseFnBranch name)

  pure $ MkDef name ty branches

parseFnBranch :: String -> Parser DefBranch
parseFnBranch name0 = do
  name <- parseIdentifier
  guard (name == name0)

  many parseSpace
  pat <- parsePattern

  guardeds <- some parseGuardedExpr

  -- parseOp ":="
  --
  -- body <- parseExpr

  parseOp ";"

  pure $ MkDefBranch pat guardeds

parseGuardedExpr :: Parser GuardedExpr
parseGuardedExpr = do
  cond <- optionalParse (BoolLit True) (parseOp "|" *> parseExpr)

  parseOp ":="
  body <- parseExpr

  pure $ MkGuardedExpr cond body

parseType :: Parser Type
parseType =
  parseBaseType
    <|>
  parseFnType

-- TODO: Parse layout types
parseBaseType :: Parser Type
parseBaseType =
  (parseString "Int" *> pure IntType)
    <|>
  (parseString "Bool" *> pure BoolType)
    <|>
  fmap AdtType go
  where
    go = do
      str <- parseTypeName
      guard (str `notElem` reservedTypes)
      pure str

    reservedTypes = ["Int", "Bool"]

parseFnType :: Parser Type
parseFnType = do
  dom <- leftType
  parseOp "->"
  cod <- parseType
  pure $ FnType dom cod
  where
    leftType = parseBaseType <|> parseBracketed (parseChar '(') (parseChar ')') parseType

