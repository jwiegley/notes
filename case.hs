module Main where

import Data.Maybe

main = print $ case Just (10 :: Int) of
  Just x | x < 10 -> x
  Just y | y > 10 -> y
  Just z -> z
