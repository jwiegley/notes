module Foldl where

main :: IO ()
main = print $ foldl (\(a, b) x -> a `seq` b `seq` (a + x, b + 2))
             (0 :: Int, 0 :: Int) ([1..10000000] :: [Int])
