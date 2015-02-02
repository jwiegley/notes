module Main where

import Prelude hiding (Functor, fmap, Monad, Maybe(..))

class Functor f where
  fmap :: (a -> b) -> (f a -> f b)

class Functor m => Monad m where
  unit :: a -> m a
  join :: m (m a) -> m a

  bind :: (a -> m b) -> m a -> m b
  bind f = join . fmap f

data Maybe a = Nothing | Just a
             deriving Show

instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just x) = Just (f x)

instance Monad Maybe where
  unit x = Just x
  join Nothing = Nothing
  join (Just Nothing) = Nothing
  join (Just (Just x)) = Just x

foo :: Maybe Int -> Maybe Int
foo = bind (Just . (+1)) . bind (Just . (+1))

main = print $ foo (Just 20)
