{-# LANGUAGE OverloadedStrings #-}

module HLens where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Distributive
import Data.Maybe
import Data.Monoid
import Data.Profunctor

data BasicLens s a = BasicLens
  { get :: s -> a
  , put :: s -> a -> s
  }

data BasicHLens s f = BasicHLens
  { hget :: forall x. s x -> f x
  , hput :: forall x. s x -> f x -> s x
  }

data Forgetful p b a = Forgetful (p b a)

instance Profunctor p => Functor (Forgetful p b) where
    fmap f (Forgetful x) = Forgetful (rmap f x)

-- profunctorLens :: (Profunctor p, Functor f) => BasicHLens (p a) f
-- profunctorLens = BasicHLens
--   { hget = Forgetful
--   , hput = \s a -> _
--   }

h :: (Distributive m1, Monad m1, Functor m2, Monad m2)
  => (b -> m1 (m2 c)) -> (a -> m1 (m2 b)) -> a -> m1 (m2 c)
h f g = liftM join . join . liftM (distribute . liftM f) . g
