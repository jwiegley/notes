module Main where

import Control.Applicative
import Control.Monad.Tardis

applyToMaximum _ m [] = do
    sendPast m
    return []
applyToMaximum f acc (x:xs) = do
    mx <- getFuture
    let y  = if x == mx then f x else x
        acc' = if x > acc then x else acc
    (:) <$> pure y <*> applyToMaximum f acc' xs

main = do
    (x,_) <- flip runTardisT (0,0) $
             applyToMaximum (+10) 0 [1,3,2,0,1]
    print x -- [1,13,2,0,1]
