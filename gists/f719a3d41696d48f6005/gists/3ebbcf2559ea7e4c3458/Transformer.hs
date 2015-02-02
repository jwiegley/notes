{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Transformer where

import Control.Monad.Trans.Either

class MonadHoist (t :: (* -> *) -> * -> *) m | t -> m where
    return' :: Monad n => m a -> t n a
    bind' :: Monad n => t n a -> (m a -> t n b) -> t n b

instance MonadHoist (EitherT e) (Either e) where
    return' = EitherT . return
    bind' (EitherT m) f = EitherT $ do
        x <- m
        runEitherT $ f x
