{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Applicative
import Data.Map

instance Ord k => Applicative (Map k) where
    (toList -> fs) <*> (toList -> vs) = fromList $ go fs vs
      where
        go [] _ = []
        go _ [] = []
        go xs@((k1,f):rest1) ys@((k2,v):rest2)
            | k1 == k2  = (k1, f v):go rest1 rest2
            | otherwise = go xs rest2 ++ go rest1 ys

main = print $ fromList [("foo", (+1)), ("bar", (+2))]
       <*> fromList [("foo", 1), ("bar", 2)]
