{-# LANGUAGE ViewPatterns #-}

module Main where

import Control.Lens
import Data.List

selectFromList :: [a] -> [Int] -> [a]
selectFromList xs (reverse . nub . sort -> idxs) =
    foldr go (length xs - 1,idxs,[]) xs ^. _3
  where
    go _ (i,[],xs) = (i-1,[],xs)
    go x (i,idx:idxs,xs)
        | i == idx  = (i-1,idxs,x:xs)
        | otherwise = (i-1,idx:idxs,xs)

main = do
    print $ selectFromList ['a' .. 'z'] [1,3,14,25]
