{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

module WriterCheck where

class Monad m => MonadWriter w m {- | m -> w -} where
    tell :: w -> m ()
    listen :: m a -> m (a, w)

foo :: MonadWriter String m => m Int
foo = do
    tell "Hello"
    listen (return 20)
    return 10
