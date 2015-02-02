{-# LANGUAGE OverloadedStrings #-}

module MySTM where

import Control.Applicative
import Control.Concurrent.STM hiding (TMVar, putTMVar, takeTMVar, newTMVar, newEmptyTMVar)
--import Control.Monad

newtype TMVar a = TMVar (TVar (Maybe a))

newEmptyTMVar = TMVar <$> newTVar Nothing
newTMVar x    = TMVar <$> newTVar (Just x)

putTMVar :: TMVar a -> a -> STM ()
putTMVar (TMVar v) x = readTVar v >>= maybe
    (writeTVar v (Just x))
    (const retry)

takeTMVar :: TMVar b -> STM b
takeTMVar (TMVar v) =
    readTVar v >>= maybe retry return

main :: IO ()
main = do
    v <- atomically newEmptyTMVar
    -- atomically $ putTMVar v 10
    print =<< atomically (takeTMVar v :: STM Int)
