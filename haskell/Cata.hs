{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE LambdaCase #-}

module Cata where

import Data.Fix

type Alg f a = f a -> a

data Cata f a = forall x. Cata (f x -> x) (x -> a)

instance Functor (Cata f) where
    fmap f (Cata alg red) = Cata alg (f . red)

algComp :: Functor f => (f a -> a) -> (f b -> b) -> f (a, b) -> (a, b)
algComp f g x = (f (fmap fst x), g (fmap snd x))

instance Functor f => Applicative (Cata f) where
    pure x = Cata undefined (const x)
    Cata falg fred <*> Cata galg gred =
        Cata (algComp falg galg) (\(f, g) -> fred f (gred g))

runCata :: Functor f => Cata f a -> Fix f -> a
runCata (Cata alg red) f = red (cata alg f)

data ListF a r = Nil | Cons a r deriving Functor

type List a = Fix (ListF a)

sumList :: Num a => Alg (ListF a) a
sumList = \case Nil -> 0; Cons x y -> x + y

lenList :: Alg (ListF a) Int
lenList = \case Nil -> 0; Cons _ r -> 1 + r

liftWithRed :: Alg f a -> (a -> b) -> Cata f b
liftWithRed = Cata

lift :: Alg f a -> Cata f a
lift = flip liftWithRed id

main :: IO ()
main = do
    let xs = Fix (Cons 10
                  (Fix (Cons 20
                        (Fix (Cons 30
                              (Fix Nil)))))) :: List Int

    print $ runCata ((,) <$> lift sumList <*> lift lenList) xs
    -- => (60,3) in a single pass over the list
