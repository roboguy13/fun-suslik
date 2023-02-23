import Criterion.Main

sll_plus1 :: [Int] -> [Int]
sll_plus1 [] = []
sll_plus1 (x:xs) = x+1 : sll_plus1 xs

main :: IO ()
main =
  let l1 = [1 .. 100000]
    in
  defaultMain
    [ bgroup "sll_plus1"
        [ bench "1" $ nf (\(xs) -> sll_plus1 xs) (l1)
        ]
    ]