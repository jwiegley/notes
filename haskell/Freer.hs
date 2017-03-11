{-# LANGUAGE GADTs #-}

module Freer where

import Control.Monad.Free
import Data.Functor.Identity
import Data.Functor.Rep

data CoyonedaR g f a where
    Coyo :: Representable g => f (Rep g) -> g a -> CoyonedaR g f a

instance Functor (CoyonedaR g f) where
    fmap f (Coyo gx h) = Coyo gx (fmap f h)

liftCoyonedaR :: f a -> CoyonedaR ((->) a) f a
liftCoyonedaR ga = Coyo ga id

lowerCoyonedaR :: Functor f => CoyonedaR g f a -> f a
lowerCoyonedaR (Coyo gx h) = fmap (index h) gx

type Freer f = Free (CoyonedaR Identity f)
