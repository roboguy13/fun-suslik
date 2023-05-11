module Testing.Test
  where


import Test.Tasty
import Test.Tasty.Ingredients.ConsoleReporter
import Test.Tasty.Golden

import System.IO
import System.Environment

import Control.Monad

import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS

import System.FilePath

import Testing.TestConfig

main :: IO ()
main = do
  args <- getArgs

  tests <- readTests <$> BS.readFile optionsPath

  let ingredients = consoleTestReporter : defaultIngredients

  defaultMainWithIngredients ingredients =<< goldenTests tests

goldenTests :: [TestConfig] -> IO TestTree
goldenTests tests = do
  fsusFiles <- findByExtension [".fsus"] testsPath
  pure $ testGroup "golden tests"
      [ goldenVsString
              baseName
              outputFile
              (runTest (lookupTestConfig baseName tests) fsusFile)
        | fsusFile <- fsusFiles
        , let baseName = takeBaseName fsusFile
        , let outputFile = replaceExtension fsusFile ".golden"
      ]

runTest :: TestConfig -> FilePath -> IO ByteString
runTest = runPika False

