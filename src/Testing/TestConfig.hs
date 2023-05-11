{-# LANGUAGE DeriveGeneric #-}

module Testing.TestConfig
  where

import GHC.Generics
import Data.Aeson

import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS

import System.FilePath
import System.Process
import Data.String

import Control.Monad

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

runPika :: Bool -> TestConfig -> FilePath -> IO ByteString
runPika isBenchmark test inputFile = do
  let testName = name test
      opts = if isBenchmark
               then "--benchmark" : options test
               else options test

  (exitCode, output, _stderrOut)
    <- readCreateProcessWithExitCode (proc pikaCmd (inputFile : opts)) ""

  when isBenchmark $ putStr output

  pure $ fromString output

