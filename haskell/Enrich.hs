{- This code is from @Profpatsch:

   https://twitter.com/profpatsch/status/988140868199739392?s=12 -}

{-# LANGUAGE FlexibleInstances #-}

module Enrich where

import Data.Monoid

-- This definition would be in another module
class Monoid a => Group a where
  inverse :: a -> a

newtype Enrich with a =
  Enrich { unrich :: with -> a }

newtype Inv a = Inv (a -> a)
type AsGroup a = Enrich (Inv a) a

-- TODO: use DerivingVia
instance (Monoid a) => Monoid (AsGroup a) where
  mempty = Enrich $ const mempty
  mappend a b = Enrich
    $ \inv -> mappend (unrich a inv) (unrich b inv)

-- No OrphanInstances is needed to instantiate
instance Monoid a => Group (AsGroup a) where
  inverse a = Enrich $ \(Inv f) -> f (unrich a (Inv f))

asGroup :: Monoid m => m -> AsGroup m
asGroup m = Enrich $ const m

main = print $
  getSum $ unrich (inverse (asGroup $ Sum 4)
                  `mappend` (asGroup $ Sum 5))
             (Inv $ \x -> (-x))
