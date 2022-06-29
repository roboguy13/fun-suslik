{-# LANGUAGE LambdaCase #-}

module Main where

import           EGraph.EGraph
import           EGraph.Rewrite

import           Nucleus.Expr
import           Nucleus.Parser

import           Nucleus.TypeChecker

import           Error.Error
import           Error.Render

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
  (pState, defs) <- getArgs >>= \case
    [fileName] -> do
      contents <- readFile fileName

      let state = initialState fileName contents

      case runParser' (parseTopLevel <* eof) state of
        (pState, Left err) -> error $ show err
        (pState, Right r) -> pure (pState, mapMaybe getDef r)
    [] -> pure (initialState "<empty>" "", [])
    _ -> error "Wrong number of arguments. Expected one or zero."

  let env = map defToExprAssoc defs
  mapM_ putStrLn $ map ppr defs
  print env

  forM_ defs $ \def ->
    case typeCheckDef def of
      Left err -> do
        hFlush stdout
        putStrLn ("\nFailed to type check the definition " ++ defName def)
        case getFirstErrorLine (statePosState pState) err of
          Just (SourcePosLine (Just offendingLine) _) -> do
            putStrLn (renderTcError offendingLine err)
          _ ->
            putStrLn (show err)
        exitFailure
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


-- NOTE: From megaparsec source (this should probably be exported):
-- | Given the name of source file and the input construct the initial state
-- for a parser.
initialState :: String -> s -> State s e
initialState name s =
  State
    { stateInput = s,
      stateOffset = 0,
      statePosState =
        PosState
          { pstateInput = s,
            pstateOffset = 0,
            pstateSourcePos = initialPos name,
            pstateTabWidth = defaultTabWidth,
            pstateLinePrefix = ""
          },
      stateParseErrors = []
    }

