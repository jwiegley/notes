module Main where

import Data.Monoid hiding (Sum)
import Control.Applicative
import Data.Functor.Identity

data Sum f g a = InL (f a) | InR (g a) deriving Show

instance (Functor f, Functor g) => Functor (Sum f g) where
    fmap f (InL x) = InL (fmap f x)
    fmap f (InR y) = InR (fmap f y)

class Natural f g where
    eta :: f a -> g a

instance (Applicative f, Applicative g, Natural g f) =>
  Applicative (Sum f g) where
    pure x = InR $ pure x
    (InL f) <*> (InL x) = InL (f <*> x)
    (InR g) <*> (InR y) = InR (g <*> y)
    (InL f) <*> (InR x) = InL (f <*> eta x)
    (InR g) <*> (InL x) = InL (eta g <*> x)

type Result e a = Monoid e => Sum (Const e) Identity a

instance Monoid e => Natural Identity (Const e) where
    eta (Identity _) = Const mempty

instance Show a => Show (Identity a) where
    show (Identity x) = show x

instance Show e => Show (Const e a) where
    show (Const x) = show x

main = do
    let x = InR (Identity 8) :: Result String Int
    print $ (*) <$> x <*> InR (Identity (7 :: Int))
    print $ (*) <$> InL (Const "foo") <*> x
    print $ (*) <$> x <*> InL (Const "foo")
    let x = InL (Const "foo") :: Result String Int
    print $ (*) <$> x <*> InL (Const "bar")
