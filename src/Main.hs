{-# LANGUAGE LambdaCase #-}

module Main where

import           EGraph.EGraph
import           EGraph.Rewrite

import           Nucleus.Expr
import           Nucleus.Parser

import           Nucleus.TypeChecker

import           Representation.Parts
import           Backend.DOT

import           Data.Maybe

import           System.Timeout
import           System.Environment
import           System.IO
import           System.Exit

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
  mapM_ putStrLn $ map ppr defs
  print env

  forM_ defs $ \def ->
    case typeCheckDef def of
      Left err -> hFlush stdout >> putStrLn ("\nFailed to type check the definition " ++ defName def ++ "\n" ++ ppr err) >> exitFailure
      Right _ -> pure ()

  repl env

repl :: Env String -> IO ()
repl env = do
  putStr ">> "
  hFlush stdout
  input <- getLine
  when (input /= ":q") $ do
    case parse (parseExpr <* eof) "<stdin>" input of
      Left err -> putStrLn $ "Parse error: " ++ show err
      Right r -> putStrLn (ppr r) >> putStrLn (ppr (eval env r))
    repl env

  -- putStrLn $ runRenderM $ renderEGraphState $ snd $ runEGraphM (test1 :: Expr ()) (pure ())
-- main = putStrLn $ runRenderM $ renderParts $ toParts test1
-- main = print $ applyRewrite rewrite1 $ toParts test1
-- main = print $ runEGraphM (test1 :: Expr ()) (pure ())

