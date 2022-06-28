module Main where

import           EGraph.EGraph
import           EGraph.Rewrite
import           Nucleus.Expr

import           System.Timeout

main :: IO ()
main = do
  timeout 20000 $
    print $ applyRewrite rewrite1 $ toParts test1
  pure ()
-- main = print $ runEGraphM (test1 :: Expr ()) (pure ())
