{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module NatTrans where

--import Control.Applicative
--import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe

class NatTrans s t where
    nmap :: forall a. s a -> t a
    -- Such that: nmap . fmap f = fmap f . nmap

instance MonadIO m => NatTrans IO m where
    nmap = liftIO

-- newtype MyMaybeT m a = MyMaybeT { runMyMaybeT :: MaybeT m a }

-- instance Monad m => Functor (MyMaybeT m) where
--     fmap f (MyMaybeT x) = MyMaybeT (liftM f x)

-- instance Monad m => Applicative (MyMaybeT m) where
--     pure = MyMaybeT . return
--     MyMaybeT f <*> MyMaybeT x = MyMaybeT (ap f x)

-- instance Monad m => Monad (MyMaybeT m) where
--     return = pure
--     MyMaybeT x >>= f = MyMaybeT $ x >>= runMyMaybeT . f

-- instance NatTrans IO (MyMaybeT IO) where
--     nmap = MyMaybeT . liftIO

main :: IO ()
main = do
    _ <- runMaybeT $ nmap $ print (10 :: Int)
    -- _ <- runMaybeT $ runMyMaybeT $ MyMaybeT $ nmap $ print (10 :: Int)
    return ()
