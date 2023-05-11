module Testing.Benchmark
  where

import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BS

import System.Environment
import System.FilePath

import Testing.TestConfig

import Control.Monad

import Test.Tasty.Golden (findByExtension)

main :: IO ()
main = do
  tests <- readTests <$> BS.readFile optionsPath

  runBenchmarks tests

runBenchmarks :: [TestConfig] -> IO ()
runBenchmarks testConfigs = do
  fsusFiles <- findByExtension [".fsus"] testsPath

  forM_ fsusFiles $ \fsusFile ->
    let baseName = takeBaseName fsusFile
    in
    runBenchmark (lookupTestConfig baseName testConfigs) fsusFile

runBenchmark :: TestConfig -> FilePath -> IO ByteString
runBenchmark = runPika True

