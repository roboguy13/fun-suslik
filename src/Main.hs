{-# LANGUAGE LambdaCase #-}

module Main where

import           EGraph.EGraph
import           EGraph.Rewrite

import           Nucleus.Expr
import           Nucleus.Parser

import           Representation.Parts
import           Backend.DOT

import           Data.Maybe

import           System.Timeout
import           System.Environment
import           System.IO

import           Text.Megaparsec

import           Control.Monad

main :: IO ()
main = do
  defs <- getArgs >>= \case
    [fileName] -> do
      contents <- readFile fileName
      case parse (parseTopLevel <* eof) fileName contents of
        Left err -> error $ show err
        Right r -> pure $ mapMaybe getDef r
    [] -> pure []
    _ -> error "Wrong number of arguments. Expected one or zero."

  let env = map defToExprAssoc defs
  print defs
  print env

  repl env

repl :: Env String -> IO ()
repl env = do
  putStr ">> "
  hFlush stdout
  input <- getLine
  when (input /= ":q") $ do
    case parse (parseExpr <* eof) "<stdin>" input of
      Left err -> putStrLn $ "Parse error: " ++ show err
      Right r -> print r >> print (eval env r)
    repl env

  -- putStrLn $ runRenderM $ renderEGraphState $ snd $ runEGraphM (test1 :: Expr ()) (pure ())
-- main = putStrLn $ runRenderM $ renderParts $ toParts test1
-- main = print $ applyRewrite rewrite1 $ toParts test1
-- main = print $ runEGraphM (test1 :: Expr ()) (pure ())
