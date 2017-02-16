{-# LANGUAGE RankNTypes #-}

module Base10 where

import Control.Lens
import Data.List (foldl')

base :: Integral a => Int -> Traversal' a Int
base n f = fmap undigs . traverse f . digs
  where
    digs :: Integral x => x -> [Int]
    digs 0 = []
    digs x = digs (fromIntegral x `div` n) ++ [fromIntegral x `mod` n]

    undigs :: Integral x => [Int] -> x
    undigs = foldl' (\num d -> fromIntegral n * num + fromIntegral d) 0
