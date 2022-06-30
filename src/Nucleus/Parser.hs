{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}

module Nucleus.Parser
  where

import           Text.Megaparsec hiding (token)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as Lexer

import           Control.Monad

import           Data.Void
import           Data.Maybe
import           Data.List

import           Nucleus.Expr

data SourcePosLine = SourcePosLine (Maybe String) SourcePos

getOffset' :: Parser SrcOffset
getOffset' = getOffset

offsetsToSourcePosList :: forall s. TraversableStream s => PosState s -> [SrcOffset] -> [SourcePosLine]
offsetsToSourcePosList posState0 =
  reverse . fst . foldl' go ([], posState0)
  where
    go :: ([SourcePosLine], PosState s) -> SrcOffset -> ([SourcePosLine], PosState s)
    go (srcPosLines, posState1) offset =
      (SourcePosLine line_maybe srcPos : srcPosLines, posState)
      where
        (line_maybe, posState) = reachOffset offset posState1
        srcPos = pstateSourcePos posState

type Parser = Parsec String String

lexeme :: Parser a -> Parser a
lexeme = Lexer.lexeme (Lexer.space space1 mzero mzero)

token :: String -> Parser SrcOffset
token str = do
  startLoc <- getOffset
  lexeme $ chunk str
  pure startLoc
  -- endLoc <- getOffset
  -- pure $ SrcSpan startLoc endLoc

parseTopLevel :: Parser [TopLevel]
parseTopLevel = some (fmap TopLevelDef parseDef)

parseDef :: Parser Def
parseDef = do
  (sigName, ty) <- parseTypeSig

  many space1

  (bndNameOff, bndName) <- parseIdent
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
  (sigNameOff, sigName) <- parseIdent
  many space1
  token ":"
  ty <- parseType
  many space1
  token ";"
  pure (sigName, ty)

parseParamList :: Parser [(SrcLoc, String)]
parseParamList =
  try ((:) <$> parseIdent <*> (some space1 *> parseParamList)) <|>
  fmap (:[]) parseIdent

parseType :: Parser (Type String)
parseType =
  try parseFnType <|>
  parseEnclosedType

basicKeyword :: (SrcLoc -> a) -> String -> Parser a
basicKeyword f str = do
  startLoc <- keyword str
  endLoc <- getOffset
  pure (f (SrcSpan startLoc endLoc))

parseEnclosedType :: Parser (Type String)
parseEnclosedType =
  (chunk "(" *> many space1 *> parseType <* many space1 <* chunk ")") <|>
  (basicKeyword BoolType "Bool") <|>
  (basicKeyword IntType "Int") <|>
  (basicKeyword UnitType "Unit") <|>
  parsePairType <|>
  parseListType <|>
  parseRefinement <|>
  fmap (uncurry TyVar) parseTyIdent

parseListType :: Parser (Type String)
parseListType = do
  startLoc <- token "List"
  ty <- parseEnclosedType
  endLoc <- getOffset
  pure $ ListType (SrcSpan startLoc endLoc) ty

parsePairType :: Parser (Type String)
parsePairType = do
  startLoc <- token "Pair"
  a <- parseEnclosedType
  some space1
  b <- parseEnclosedType
  endLoc <- getOffset
  pure (PairType (SrcSpan startLoc endLoc) a b)

parseFnType :: Parser (Type String)
parseFnType = do
  startLoc <- getOffset
  src <- parseEnclosedType
  many space1
  token "->"
  tgt <- parseType
  endLoc <- getOffset
  pure (Arr (SrcSpan startLoc endLoc) src tgt)

parseRefinement :: Parser (Type String)
parseRefinement = do
  startLoc <- token "{"
  (_, ident) <- parseIdent
  many space1

  token ":"
  ty <- parseType
  many space1

  token "|"
  cond <- parseRefinementCondition
  many space1

  token "}"
  endLoc <- getOffset
  pure (Refinement (SrcSpan startLoc endLoc) ident ty cond)

parseRefinementCondition :: Parser [ExprEq Void String]
parseRefinementCondition =
  try ((:) <$> parseExprEq <*> (many space1 *> token "&" *> parseRefinementCondition)) <|>
  fmap (:[]) parseExprEq

parseExprEq :: Parser (ExprEq Void String)
parseExprEq = do
  lhs <- try parseApply <|> parseEnclosedExpr
  many space1
  token "="
  rhs <- parseExpr
  pure (wrappedExpr lhs :=: wrappedExpr rhs)

parseExpr :: Parser (Expr String)
parseExpr = try parseCompose <|> parseExpr1

parseExpr1 :: Parser (Expr String)
parseExpr1 =
  try parseLambda <|>
  try parseAdd <|>
  try parseSub <|>
  try parseMul <|>
  try parseAnd <|>
  try parseOr <|>
  try parseApply <|>
  parseEnclosedExpr

parseEnclosedExpr :: Parser (Expr String)
parseEnclosedExpr =
  (chunk "(" *> many space1 *> parseExpr <* many space1 <* chunk ")") <|>
  try parseInt <|>
  parseBool <|>
  try (fmap (uncurry Comb) parseComb) <|>
  parseVar <|>
  parseList

parseList :: Parser (Expr String)
parseList = try parseNil <|> do
  startLoc <- token "["
  list <- go
  many space1
  chunk "]"
  endLoc <- getOffset
  let srcSpan = SrcSpan startLoc endLoc
  pure $ foldr (\x xs -> Comb srcSpan Cons :@ x :@ xs) (Comb srcSpan Nil) list
  where
    go =
      try ((:) <$> parseExpr <*> (many space1 *> token "," *> go)) <|>
      fmap (:[]) parseExpr

parseNil :: Parser (Expr String)
parseNil = do
  startLoc <- token "["
  chunk "]"
  endLoc <- getOffset
  pure (Comb (SrcSpan startLoc endLoc) Nil)

parseVar :: Parser (Expr String)
parseVar = uncurry Var <$> parseIdent

parseInt :: Parser (Expr String)
parseInt = do
  startLoc <- getOffset
  endLoc <- getOffset
  IntLit (SrcSpan startLoc endLoc) . read <$> some numberChar

parseBool :: Parser (Expr String)
parseBool =
  (basicKeyword (`BoolLit` False) "False") <|>
  (basicKeyword (`BoolLit` True) "True")

-- TODO: Figure out how to deal with application SrcLocs here
parseBinOp :: String -> (SrcLoc -> a -> b -> c) -> Parser a -> Parser b -> Parser c
parseBinOp name op p q = do
  startLoc <- getOffset
  x <- p
  many space1
  token name
  y <- q
  endLoc <- getOffset
  pure (op (SrcSpan startLoc endLoc) x y)

parseAdd :: Parser (Expr String)
parseAdd = parseBinOp "+" Add parseEnclosedExpr parseExpr

parseSub :: Parser (Expr String)
parseSub = parseBinOp "-" Sub parseEnclosedExpr parseExpr

parseMul :: Parser (Expr String)
parseMul = parseBinOp "*" Mul parseEnclosedExpr parseExpr

parseAnd :: Parser (Expr String)
parseAnd =
  parseBinOp "&&" (\loc x y -> Comb loc And :@ x :@ y) parseEnclosedExpr parseExpr

parseOr :: Parser (Expr String)
parseOr =
  parseBinOp "||" (\loc x y -> Comb loc Or :@ x :@ y) parseEnclosedExpr parseExpr

parseCompose :: Parser (Expr String)
parseCompose = do
  startLoc <- getOffset
  x <- parseExpr1
  some space1
  chunk "."
  some space1
  y <- parseExpr
  endLoc <- getOffset
  pure (Comb (SrcSpan startLoc endLoc) ComposeF :@ x :@ y)

parseApply :: Parser (Expr String)
parseApply = try $ foldl1 (:@) <$> go
  where
    go =
      try ((:) <$> parseEnclosedExpr <*> (some space1 *> go)) <|>
      fmap (:[]) parseEnclosedExpr

parseTyIdent :: Parser (SrcLoc, String)
parseTyIdent = do
  startLoc <- getOffset
  ident <- (:) <$> lowerChar <*> many (alphaNumChar <|> char '_')
  endLoc <- getOffset
  pure (SrcSpan startLoc endLoc, ident)

parseIdent :: Parser (SrcLoc, String)
parseIdent = do
  startLoc <- getOffset
  ident <- (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_')
  endLoc <- getOffset
  pure (SrcSpan startLoc endLoc, ident)

delimiter :: Parser ()
delimiter =
  eof <|>
  space1 <|>
  void (satisfy (not . (`elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ "_"))))

keyword :: String -> Parser SrcOffset
keyword str = do
  loc <- getOffset
  chunk str <* lookAhead delimiter
  pure loc

keywordToken :: String -> Parser SrcOffset
keywordToken str = token str <* lookAhead delimiter

parseLambda :: Parser (Expr String)
parseLambda = do
  startLoc <- token "\\"
  (_, x) <- parseIdent
  many space1
  token "->"
  body <- parseExpr
  endLoc <- getOffset

  pure $ lam (SrcSpan startLoc endLoc) x body

comb :: String -> a -> Parser a
comb str c = keyword str *> pure c

-- TODO: Replace with an implementation using an Enum instance for
-- Combinator and Ppr
parseComb :: Parser (SrcLoc, Combinator)
parseComb = do
  startLoc <- getOffset
  r <- go
  endLoc <- getOffset
  pure (SrcSpan startLoc endLoc, r)
  where
    go =
      comb "const" ConstF <|>
      comb "compose" ComposeF <|>
      comb "nil" Nil <|>
      comb "cons" Cons <|>
      comb "head" Head <|>
      comb "tail" Tail <|>
      comb "foldr" Foldr <|>
      comb "scanr" Scanr <|>
      comb "map" Map <|>
      comb "sum" Sum <|>
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

