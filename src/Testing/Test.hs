{-# LANGUAGE DeriveGeneric #-}

module Testing.Test
  where


import Test.Tasty
import Test.Tasty.Ingredients.ConsoleReporter
import Test.Tasty.Golden

import System.FilePath

import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS
import Data.String

import Data.Aeson

import System.Process
import System.IO

import GHC.Generics

data TestConfig =
  TestConfig
  { name :: String
  , options :: [String]
  }
  deriving (Generic)

instance FromJSON TestConfig

testsPath :: FilePath
testsPath = "./tests"

optionsPath :: FilePath
optionsPath = testsPath </> "options.json"

pikaCmd :: FilePath
pikaCmd = "./fun-suslik.sh"

main :: IO ()
main = do
  tests <- readTests <$> BS.readFile optionsPath

  let ingredients = consoleTestReporter : defaultIngredients

  defaultMainWithIngredients ingredients =<< goldenTests tests

lookupTestConfig :: String -> [TestConfig] -> TestConfig
lookupTestConfig testName [] = error $ "TestConfig not found in " ++ optionsPath ++ ": " ++ show testName
lookupTestConfig testName (test : rest)
  | name test == testName = test
  | otherwise             = lookupTestConfig testName rest

readTests :: ByteString -> [TestConfig]
readTests input =
  case decode input of
    Nothing -> error $ "Cannot parse " ++ optionsPath
    Just tests -> tests

goldenTests :: [TestConfig] -> IO TestTree
goldenTests tests = do
  fsusFiles <- findByExtension [".fsus"] testsPath
  pure $ testGroup "golden tests"
      [ goldenVsString
              baseName
              outputFile
              (runTest (lookupTestConfig baseName tests) fsusFile outputFile)
        | fsusFile <- fsusFiles
        , let baseName = takeBaseName fsusFile
        , let outputFile = replaceExtension fsusFile ".golden"
      ]

runTest :: TestConfig -> FilePath -> FilePath -> IO ByteString
runTest test inputFile outputFile = do
  let testName = name test
      opts = options test

  (exitCode, output, _stderrOut)
    <- readCreateProcessWithExitCode (proc pikaCmd (inputFile : opts)) ""

  pure $ fromString output

