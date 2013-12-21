{-# LANGUAGE BangPatterns #-}

module Main where

foo !x = 10

bar x = x `seq` 10

main = do
    putStrLn $ "foo.."
    print $ foo undefined
    putStrLn $ "bar.."
    print $ bar undefined
