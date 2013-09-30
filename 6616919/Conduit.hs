{-# OPTIONS_GHC -fno-warn-orphans #-}

module Conduit where

import Control.Comonad
import Control.Monad.Par

instance Comonad Par where
    extract = runPar
    extend f m = return (f m)

main :: IO ()
main = do
    print $ runPar $ f (+1) (10 :: Int)
    print $ runPar $ extend g $ f (+1) (10 :: Int)
  where
    f :: NFData b => (a -> b) -> a -> Par b
    f k x = get =<< spawn (return (k x))

    g :: Num a => Par a -> a
    g m = let x = runPar m
          in x + 100
