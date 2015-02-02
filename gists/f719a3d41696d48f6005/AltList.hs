{-# LANGUAGE OverloadedStrings #-}

module AltList where

import Control.Applicative
import Control.Monad
import Data.Distributive
import Control.Monad.Free
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.List
import Data.Monoid

type AltList a b = Free ((,,) a b) (Maybe a)

foo :: (Applicative m, Distributive m)
    => ((a -> b -> c) -> e -> f -> g) -> (a -> b -> m c) -> e -> f -> m g
foo k h e f = k <$> fmap curry (distribute (uncurry h)) <*> pure e <*> pure f

main :: IO ()
main = undefined
