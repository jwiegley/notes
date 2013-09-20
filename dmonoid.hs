{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module DMonoid where

import Data.Monoid

newtype DMonoid a = DMonoid { getDM :: Endo a } deriving Monoid

toDM :: Monoid a => a -> DMonoid a
toDM m = DMonoid $ Endo (m <>)

fromDM :: Monoid a => DMonoid a => a
fromDM (DMonoid dm) = appEndo dm mempty

main :: IO ()
main =
    print $ fromDM $ toDM [1 :: Int] <> toDM [2] <> toDM [3]
