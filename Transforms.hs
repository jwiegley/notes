{-# LANGUAGE MultiParamTypeClasses #-}

module Transforms where

import Prelude hiding (Functor, fmap, head, reverse)

class Functor f where
  fmap :: (a -> b) -> (f a -> f b)

class Functor f => Transform f where
  transform :: Functor g => (f a -> f b) -> (g a -> g b)

data Identity a = Identity { runIdentity :: a }
                deriving Show

instance Functor Identity where
  fmap f x = Identity $ f (runIdentity x)

instance Transform Identity where
  transform f = fmap (runIdentity . f . Identity)

adder :: Identity Int -> Identity Int
adder = fmap (1+)

data List a = Nil
            | Cons a (List a)
            deriving Show

instance Functor List where
  fmap _ Nil = Nil
  fmap f (Cons x y) = Cons (f x) (fmap f y)

instance Transform List where
  transform f = fmap (head . f . flip Cons Nil)

head :: List a -> a
head Nil        = error "Head of empty list"
head (Cons x _) = x

tail :: List a -> List a
tail Nil         = error "Tail of empty list"
tail (Cons _ xs) = xs

cons :: a -> List a -> List a
cons y xs = Cons y xs

snoc :: List a -> a -> List a
snoc Nil y         = Cons y Nil
snoc (Cons x xs) y = Cons x (xs `snoc` y)

reverse :: List a -> List a
reverse Nil         = Nil
reverse (Cons x xs) = reverse xs `snoc` x

main :: IO ()
main = do
  print $ transform adder (Cons 20 Nil :: List Int)
  print $ transform reverse (Identity 20 :: Identity Int)
