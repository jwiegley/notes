{-# OPTIONS_GHC -fno-warn-orphans #-}

module Conduit where

import Control.Comonad
import Control.Monad.Par

instance Comonad Par where
    extract = runPar
    extend f m = get =<< spawn (return (f m))

duplicate :: NFData (Par a) => Par a -> Par (Par a)
duplicate m = get =<< spawnP m

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
