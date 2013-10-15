{-# LANGUAGE DeriveFunctor #-}

module Monads where

import Data.Monoid

newtype Compose f g a = Compose (f (g a)) deriving Functor

data MonoidF m = MEmpty
               | MAppend m m deriving Functor

newtype Sum a = Sum a deriving (Show, Functor)

newtype Fix f = Mu { unFix :: f (Fix f) }

type Algebra f a = f a -> a

algsum :: Num a => MonoidF a -> a
algsum MEmpty = 0
algsum (MAppend x y) = x + y

memptyF :: Algebra MonoidF (Sum Int) -> Sum Int
memptyF alg = alg MEmpty

mappendF :: Algebra MonoidF Int -> Int -> Int -> Int
mappendF alg x y = alg (MAppend x y)

type MonoidAlg = Fix MonoidF

cata :: Functor f => (f b -> b) -> Fix f -> b
cata alg = alg . fmap (cata alg) . unFix

type Free f a = Fix (Compose (Either a) f)

iter :: Functor f => (f a -> a) -> Free f a -> a
iter _ (Mu (Compose (Left a))) = a
iter phi (Mu (Compose (Right m))) = phi (fmap (iter phi) m)

instance Monoid (MonoidF m) where
    mempty = MEmpty
    mappend x y = MAppend x y

main :: IO ()
main =
    print $ iter algsum $
        Mu (Compose
            (Right
             (MAppend
              (Mu (Compose (Right
                            (MAppend
                             (Mu (Compose (Left 10)))
                             (Mu (Compose (Left 20)))))))
              (Mu (Compose (Left 30))))))
