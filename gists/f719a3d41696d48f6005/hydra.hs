{-# LANGUAGE BangPatterns #-}

import Prelude

chop :: Int -> Int -> Int
chop  1 !count = count
chop !n !count = chop (pred n) (pred n * count)

main :: IO ()
main = print $ chop 12 1
