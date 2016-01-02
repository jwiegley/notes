{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveFunctor #-}

module FreeMtlEquiv where

import Control.Monad
import Control.Monad.Free

data AlgF r = Add r r
            | Sub r r
            deriving Functor

type Alg = Free AlgF

add :: a -> a -> Alg a
add = (liftF .) . Add

sub :: a -> a -> Alg a
sub = (liftF .) . Sub

class MonadAlg m a where
    madd :: a -> a -> m a
    msub :: a -> a -> m a

freeFoo :: Alg Int
freeFoo = do
    x <- add (1 :: Int) 2
    y <- sub x 4
    z <- sub 20 30
    add z y

mtlFoo :: (Monad m, MonadAlg m Int) => m Int
mtlFoo = do
    x <- madd (1 :: Int) 2
    y <- msub x 4
    z <- msub 20 30
    madd z y

freeToMtl :: (Monad m, MonadAlg m Int) => Alg Int -> m Int
freeToMtl = iterM phi
  where
    phi (Add x y) = join $ liftM2 madd x y
    phi (Sub x y) = join $ liftM2 msub x y

instance MonadAlg AlgF a where
    madd = Add
    msub = Sub

mtlToFree :: (Monad m, MonadAlg m Int) => m Int -> Alg Int
mtlToFree = undefined
