module Main where

import Criterion
import Criterion.Main
import Control.Monad hiding (sequence)
import Prelude hiding (sequence)
import System.IO.Unsafe

-- | Evaluate each action in the sequence from left to right,
-- and collect the results.
sequence :: Monad m => [m a] -> m [a]
{-# INLINE sequence #-}
sequence ms = go (return []) ms
            where
              go z []     = z
              go z (m:ms) = do
                  x <- m
                  xs <- go z ms
                  return $ (x:xs)

-- -- | Evaluate each action in the sequence from left to right,
-- -- and ignore the results.
-- sequence_        :: Monad m => [m a] -> m ()
-- {-# INLINE sequence_ #-}
-- sequence_ ms     =  foldr (>>) (return ()) ms

sequence' :: Monad m => [m a] -> m [a]
{-# INLINE sequence' #-}
sequence' l = go l id
  where
    go []     dlist = return $ dlist []
    go (m:ms) dlist = do x <- m
                         go ms (dlist . (x:))

foo :: [Int] -> IO [Int]
foo = foldM (\m x -> return (x:m)) (return 0)

stress :: Int -> ([IO Int] -> IO [Int]) -> IO Int
stress cnt f = do
    l <- f (replicate cnt $ return 1)
    return $ head l

go = (unsafePerformIO .) . stress

main =
  defaultMain [
      bench "sequence"   $ nf (go 1000000) sequence
      -- , bench "sequence_"  $ nf stress sequence_
      , bench "sequence'"  $ nf (go 1000000) sequence'
      -- , bench "sequence_'" $ nf stress sequence_'
      ]
