{-# LANGUAGE OverloadedStrings #-}

module Coy where

import Data.Functor.Identity

data Coyoneda f a = forall b. Coyoneda (b -> a) (f b)

instance Functor (Coyoneda f) where
    fmap f (Coyoneda k x) = Coyoneda (f . k) x

liftCoyeneda :: f a -> Coyoneda f a
liftCoyeneda = Coyoneda id

lowerCoyeneda :: Functor f => Coyoneda f a -> f a
lowerCoyeneda (Coyoneda k x) = fmap k x

main :: IO ()
main = do
    let z = Identity 10
    let x = liftCoyeneda z
        y = fmap (+1) x
        y' = fmap (+1) y
        y'' = fmap (+1) y'

    let z = lowerCoyeneda y''
        z' = fmap (+1) (liftCoyeneda z)
        z'' = fmap (+1) z'
        z''' = fmap (+1) z''

    print $ runIdentity $ lowerCoyeneda z'''
