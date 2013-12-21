{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module IOState where

import Control.DeepSeq
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State.Class
import Control.Monad.Trans.State (execStateT)
import Criterion
import Criterion.Main
import Data.IORef
import System.IO.Unsafe

global :: IORef Int
{-# NOINLINE global #-}
global = unsafePerformIO $ newIORef 0

data IOState s a = IOState { getIOState :: IO a } deriving (Functor)

runIOState :: IOState Int a -> Int -> IO Int
runIOState (IOState m) s = do
    writeIORef global s
    _ <- m
    readIORef global

instance Monad (IOState s) where
    return = IOState . return
    IOState m >>= f = IOState $ m >>= getIOState . f

instance MonadIO (IOState s) where
    liftIO = IOState

instance MonadState Int (IOState Int) where
    get = IOState $ readIORef global
    put s = IOState $ writeIORef global s

instance NFData a => NFData (IO a) where
    rnf = unsafePerformIO . fmap rnf

getPut :: (Num a, MonadState a m, MonadIO m) => Int -> m a
getPut n = do
    x <- get
    put $! x + 1
    if n == 0 then return x else getPut (pred n)

main = do
    go 1 runIOState
    defaultMain
        [ bench "StateT Int IO" $ nf (go 100) execStateT
        , bench "IOState Int"   $ nf (go 100) runIOState
        ]
  where
    go :: (Num a, MonadState a m, MonadIO m)
       => Int -> (m [a] -> Int -> IO Int) -> IO Int
    go n f = f (replicateM n (getPut 100)) 1
