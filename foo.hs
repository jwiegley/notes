{-# LANGUAGE ExistentialQuantification #-}

module Main where

import Control.Lens

-- When f is a Functor, CoYoneda f is isomorphic to f.
data CoYoneda f a = forall s. CoYoneda (f s) (s -> a)

instance Functor (CoYoneda f) where
    fmap g (CoYoneda x k) = CoYoneda x (g . k)

lowerCoYoneda :: Functor f => CoYoneda f a -> f a
lowerCoYoneda (CoYoneda x k) = fmap k x

liftCoYoneda :: f a -> CoYoneda f a
liftCoYoneda x = CoYoneda x id

-- When f is a Functor, Yoneda f is isomorphic to f.
data Yoneda f a = Yoneda (forall r. (a -> r) -> f r)

instance Functor (Yoneda f) where
    fmap g (Yoneda k) = Yoneda $ \h -> k (h . g)

lowerYoneda :: Yoneda f a -> f a
lowerYoneda (Yoneda k) = k id

liftYoneda :: Functor f => f a -> Yoneda f a
liftYoneda a = Yoneda $ \k -> fmap k a

main :: IO ()
main = undefined

{-
y = liftCoYoneda [10] = CoYoneda [10] id
fmap g y = CoYoneda [10] $ id . g
fmap h y = CoYoneda [10] $ id . h . g
fmap i y = CoYoneda [10] $ id . i . h . g
lowerCoYoneda (CoYoneda [10] $ id . i . h . g) = fmap (id . i . h . g) [10]

y = liftYoneda [10] = Yoneda $ \f -> fmap f [10]
fmap g y = Yoneda $ \x -> fmap (x . g) [10]
fmap h y = Yoneda $ \x -> fmap (x . h . g) [10]
fmap i y = Yoneda $ \x -> fmap (x . i . h. g) [10]
lowerYoneda (Yoneda $ \x -> fmap (x . i . h. g) [10]) = fmap (id . i . h . g) [10]
-}

-- Yoneda IO a = forall b. (a -> b) -> IO b