module Main where

import           EGraph.EGraph
import           EGraph.Rewrite
import           Nucleus.Expr
import           Representation.Parts
import           Backend.DOT

import           System.Timeout

main :: IO ()
main =
  putStrLn $ runRenderM $ renderEGraphState $ snd $ runEGraphM (test1 :: Expr ()) (pure ())
-- main = putStrLn $ runRenderM $ renderParts $ toParts test1
-- main = print $ applyRewrite rewrite1 $ toParts test1
-- main = print $ runEGraphM (test1 :: Expr ()) (pure ())
