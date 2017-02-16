{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.DeepSeq
import Criterion
import Criterion.Main
import Data.Foldable as Foldable
import Data.IntMap as M
import Linear.Sparse
import Linear.Vector
import System.Remote.Monitoring

exercise :: (Additive f, Num a) => Int -> f a -> f a
exercise n x = Foldable.foldr (\x y -> seq x $ seq y $ x ^+^ y)
                              zero (replicate n x)

main :: IO ()
main = do
    forkServer "localhost" 8000
    defaultMain
        [ bench "using IntMap over 1000000 iterations"
          $ nf (exercise 1000000) (fromList [(1,10)] :: IntMap Int)
        , bench "using Sparse over 1000000 iterations"
          $ nf (exercise 1000000) (Single 1 10 :: Sparse IntMap Int Int) ]
