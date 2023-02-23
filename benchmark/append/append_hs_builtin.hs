import Criterion.Main

myapp :: [Int] -> [Int] -> [Int]
myapp [] ys = ys
myapp (x:xs) ys = x : myapp xs ys

main :: IO ()
main =
  let l1 = [1 .. 100000]
      l2 = [1 .. 100000]
  in
  defaultMain
    [ bgroup "myapp"
        [ bench "1" $ nf (\(xs, ys) -> myapp xs ys) (l1, l2)
        ]
    ]