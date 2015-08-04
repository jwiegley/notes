{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad
import Data.List (foldl')
import Data.SBV

main = forM_ [5..10] $ \n -> do
    result <- sat $ do
        xs :: [SInteger] <- replicateM (1+ n) exists_
        forM_ xs $ constrain . (.> 0)
        return $ last xs^n .== foldl' ((+) . (^n)) 0 (init xs)
    putStrLn $ "n = " ++ show n ++ ": " ++ show result
