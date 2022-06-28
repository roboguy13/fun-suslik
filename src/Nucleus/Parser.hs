module Nucleus.Parser
  where

import           Text.Megaparsec hiding (token)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer

import           Control.Monad

import           Data.Void
import           Data.Maybe

import           Nucleus.Expr

type Parser = Parsec String String

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme (Lexer.space space1 mzero mzero)

token :: String -> Parser String
token = lexeme . chunk

parseDef :: Parser Def
parseDef = do
  (sigName, ty) <- parseTypeSig

  many space1

  bndName <- parseIdent
  guard (sigName == bndName)
  many space1

  params <- fmap (fromMaybe []) (optional parseParamList)
  many space1

  token ":="

  body <- parseExpr
  many space1
  token ";"

  pure (Def { defType = ty, defBinding = (bndName, params, body) })

parseTypeSig :: Parser (String, Type String)
parseTypeSig = do
  sigName <- parseIdent
  many space1
  token ":"
  ty <- parseType
  many space1
  token ";"
  pure (sigName, ty)

parseParamList :: Parser [String]
parseParamList =
  try ((:) <$> parseIdent <*> (some space1 *> parseParamList)) <|>
  fmap (:[]) parseIdent

parseType :: Parser (Type String)
parseType =
  try parseFnType <|>
  parseEnclosedType

parseEnclosedType :: Parser (Type String)
parseEnclosedType =
  (token "(" *> parseType <* token ")") <|>
  (chunk "Bool" *> pure BoolType) <|>
  (chunk "Int" *> pure IntType) <|>
  parseListType <|>
  parseRefinement <|>
  fmap TyVar parseTyIdent

parseListType :: Parser (Type String)
parseListType = do
  token "List"
  ListType <$> parseEnclosedType

parseFnType :: Parser (Type String)
parseFnType = do
  src <- parseEnclosedType
  many space1
  token "->"
  tgt <- parseType
  pure (src :-> tgt)

parseRefinement :: Parser (Type String)
parseRefinement = do
  token "{"
  ident <- parseIdent
  many space1
  token ":"
  ty <- parseType
  many space1
  token "|"
  cond <- parseRefinementCondition
  many space1
  token "}"
  pure (Refinement ident ty cond)

parseRefinementCondition :: Parser [ExprEq Void String]
parseRefinementCondition =
  try ((:) <$> parseExprEq <*> (many space1 *> token "&" *> parseRefinementCondition)) <|>
  fmap (:[]) parseExprEq

parseExprEq :: Parser (ExprEq Void String)
parseExprEq = do
  lhs <- parseExpr
  many space1
  token "="
  rhs <- parseExpr
  pure (wrappedExpr lhs :=: wrappedExpr rhs)

parseExpr :: Parser (Expr String)
parseExpr =
  try parseAdd <|>
  try parseSub <|>
  try parseMul <|>
  try parseAnd <|>
  try parseOr <|>
  try parseApply <|>
  try parseEnclosedExpr

parseEnclosedExpr :: Parser (Expr String)
parseEnclosedExpr =
  (token "(" *> parseExpr <* token ")") <|>
  try parseInt <|>
  parseBool <|>
  fmap Comb parseComb <|>
  parseVar

parseVar :: Parser (Expr String)
parseVar = Var <$> parseIdent

parseInt :: Parser (Expr String)
parseInt = IntLit . read <$> some numberChar

parseBool :: Parser (Expr String)
parseBool =
  (token "False" *> pure (BoolLit False)) <|>
  (token "True" *> pure (BoolLit True))

parseBinOp :: String -> (a -> b -> c) -> Parser a -> Parser b -> Parser c
parseBinOp name op p q = do
  x <- p
  many space1
  token name
  y <- q
  pure (op x y)

parseAdd :: Parser (Expr String)
parseAdd = parseBinOp "+" Add parseEnclosedExpr parseExpr

parseSub :: Parser (Expr String)
parseSub = parseBinOp "-" Sub parseEnclosedExpr parseExpr

parseMul :: Parser (Expr String)
parseMul = parseBinOp "*" Mul parseEnclosedExpr parseExpr

parseAnd :: Parser (Expr String)
parseAnd =
  parseBinOp "&&" (\x y -> Comb And :@ x :@ y) parseEnclosedExpr parseExpr

parseOr :: Parser (Expr String)
parseOr =
  parseBinOp "||" (\x y -> Comb Or :@ x :@ y) parseEnclosedExpr parseExpr

parseApply :: Parser (Expr String)
parseApply = do
  f <- parseEnclosedExpr
  xs <- some (some space1 *> parseEnclosedExpr)
  pure $ foldl1 (:@) (f:xs)

parseTyIdent :: Parser String
parseTyIdent =
  (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')

parseIdent :: Parser String
parseIdent =
  (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_')

comb :: String -> a -> Parser a
comb str c = chunk str *> pure c

parseComb :: Parser Combinator
parseComb =
  comb "const" ConstF <|>
  comb "compose" ComposeF <|>
  comb "nil" Nil <|>
  comb "cons" Cons <|>
  comb "head" Head <|>
  comb "tail" Tail <|>
  comb "foldr" Foldr <|>
  comb "scanr" Scanr <|>
  comb "pair" Pair <|>
  comb "dup" Dup <|>
  comb "fst" Fst <|>
  comb "snd" Snd <|>
  comb "swap" Swap <|>
  comb "pairJoin" PairJoin <|>
  comb "unit" Unit <|>
  comb "ifThenElse" IfThenElse <|>
  comb "le" Le <|>
  comb "eq" IntEq <|>
  comb "not" Not <|>
  comb "and" And <|>
  comb "or" Or

