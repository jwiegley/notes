{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Forget where

import Control.Monad.IO.Class

data Foo = Foo (forall m. MonadIO m => Int -> m Int)

instance Show Foo where
    show _ = "Foo"

data FooCPS =
    FooCPS (forall m r. (MonadIO m => Int -> m Int, (MonadIO m => Int -> m Int) -> r))

instance Show FooCPS where
    show _ = "FooCPS"

data MyMonad a = MyMonad

instance Functor MyMonad where
    fmap _ MyMonad = MyMonad

instance Applicative MyMonad where
    pure _ = MyMonad
    MyMonad <*> MyMonad = MyMonad

instance Monad MyMonad where
    return _ = MyMonad
    MyMonad >>= _ = MyMonad

instance MonadIO MyMonad where
    liftIO _ = MyMonad

foo :: Int -> MyMonad Int
foo = undefined

main :: IO ()
main = do
    -- print $ Foo foo
    print $ FooCPS (foo, \k -> foo)
