module Main where

import Control.Applicative
import Control.Monad.Tardis
import Criterion
import Criterion.Main
import Data.Functor.Identity

applyToMaximum _ m [] = do
    sendPast m
    return []
applyToMaximum f acc (x:xs) = do
    mx <- getFuture
    let y  = if x == mx then f x else x
        acc' = if x > acc then x else acc
    (:) <$> pure y <*> applyToMaximum f acc' xs

tardVersion :: (Int -> Int) -> [Int] -> [Int]
tardVersion f xs =
    runIdentity $ do
        (x,_) <- flip runTardisT (0,0) $ applyToMaximum f 0 xs
        return x

naiveVersion :: (Int -> Int) -> [Int] -> [Int]
naiveVersion f xs =
    let x = maximum xs in map (\y -> if y == x then f y else y) xs

mapmax :: (Ord a) => (a -> a) -> [a] -> [a]
mapmax _ [] = []
mapmax f (x:xs) = mapmax' x xs
  where
  mapmax' mx [] = [f mx]
  mapmax' mx (x:xs) =
    if mx < x
    then mx : mapmax' x xs
    else x : mapmax' mx xs

main = do
    let xs = [1,3,2,0,1]
    print $ tardVersion (+10) xs
    print $ naiveVersion (+10) xs
    print $ mapmax (+10) xs
    defaultMain
        [ bench "tardis" $ nf (tardVersion (+10)) xs
        , bench "naive"  $ nf (naiveVersion (+10)) xs
        , bench "mapmax" $ nf (mapmax (+10)) xs
        ]
