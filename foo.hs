{-# LANGUAGE ExistentialQuantification #-}

module Main where

-- When f is a Functor, CoYoneda f is isomorphic to f.
data CoYoneda f a = forall x. CoYoneda (f x) (x -> a)

instance Functor (CoYoneda f) where
    fmap f (CoYoneda tr g) = CoYoneda tr (f . g)

lowerCoYoneda :: Functor f => CoYoneda f a -> f a
lowerCoYoneda (CoYoneda tr f) = fmap f tr

liftCoYoneda :: f Int -> CoYoneda f Int
liftCoYoneda tr = CoYoneda tr id

-- When f is a Functor, CoYoneda f is isomorphic to f.
data Yoneda f a = Yoneda (forall x. (a -> x) -> f x)

instance Functor (Yoneda f) where
    fmap f (Yoneda k) = Yoneda $ \x -> k (x . f)

lowerYoneda :: Yoneda f a -> f a
lowerYoneda (Yoneda f) = f id

liftYoneda :: Functor f => f Int -> Yoneda f Int
liftYoneda a = Yoneda $ \f -> fmap f a

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
