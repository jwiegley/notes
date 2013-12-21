{-# LANGUAGE BangPatterns #-}

module Main where

import Data.Conduit
import Data.Conduit.List as CL

a :: (Monad m) => Int -> m Int
a !x = return $! x + 1

main = do
   let iternum = 1000000
   sourceList [1..iternum]
       $= CL.mapM (\(!i) -> a $! (iternum-i))
       $$ CL.mapM_ print
