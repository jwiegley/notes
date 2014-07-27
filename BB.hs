{-# LANGUAGE RankNTypes #-}

module BB where

import Control.Applicative
import Control.Monad

fromListM :: IO [a] -> r -> (a -> r -> IO r) -> IO r
fromListM m z yield = do
    xs <- m
    foldM (flip yield) z xs

toListM :: (forall r. r -> (a -> r -> IO r) -> IO r) -> IO [a]
toListM await = await [] (\x xs -> return (x:xs))
