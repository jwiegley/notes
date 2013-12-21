{-# LANGUAGE ImplicitParams #-}

module Main where

import Data.Reflection

foo :: (?bar :: Int) => Int -> Int
foo x = x + ?bar

baz :: (Given Int, Given Float) => Int -> Int
baz x = (given :: Int) + floor (given :: Float) + x

main :: IO ()
main = do
    do let ?bar = 10
       print $ foo 5
    print $ give (10 :: Int) $ give (2.0 :: Float) $ baz 6
    print $ give (2.0 :: Float) $ give (10 :: Int) $ baz 6
