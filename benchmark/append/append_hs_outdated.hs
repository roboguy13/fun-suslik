import Text.Printf
import Control.DeepSeq
import System.CPUTime
myapp :: [Int] -> [Int] -> [Int]
myapp [] ys = ys
myapp (x:xs) ys = x : myapp xs ys

benchmark :: [Int] -> [Int] -> IO Integer
benchmark in1 in2 = do
                     start <- getCPUTime
                     let r = myapp in1 in2
                     end <- r `deepseq` getCPUTime
                     return (end - start)

main =
  let l1 = [1 .. 100000] in
  let l2 = [1 .. 100000] in
  do 
   result <- benchmark l1 l2
   let tm = (fromIntegral result) / (10^12)
   printf "Computation time: %0.5f sec\n" (tm :: Double)

