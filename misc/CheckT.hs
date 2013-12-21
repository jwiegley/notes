{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CheckT where

import Control.Monad hiding (mapM)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Data.IORef
import Data.Traversable
import Prelude hiding (mapM)

newtype CheckT m a = CheckT { getCheckT :: ReaderT (m Bool) m (Maybe a) }
    deriving Functor

runCheckT :: Monad m => m Bool -> CheckT m a -> m (Maybe a)
runCheckT approve (CheckT m) = do
    x <- approve
    if x
        then runReaderT m approve
        else return Nothing

instance Monad m => Monad (CheckT m) where
    return = CheckT . return . Just
    CheckT m >>= f = CheckT $ do
        x <- m
        res <- lift =<< ask
        if res
            then liftM join $ mapM (getCheckT . f) x
            else return Nothing

instance MonadTrans CheckT where
    lift = CheckT . liftM Just . lift

main :: IO ()
main = do
    counter <- newIORef (0 :: Int)
    x <- runCheckT (approve counter) $ do
        lift $ putStrLn "step 1"
        lift $ do
            putStrLn "These statements"
            putStrLn "are not checked"
            putStrLn "individually"
            putStrLn "but only the whole block"
        lift $ putStrLn "step 2"
        lift $ putStrLn "step 3"
        lift $ putStrLn "step 4"
    print x
  where
    approve ctr = do
        count <- readIORef ctr
        modifyIORef ctr (+1)
        putStrLn "approve?"
        return $ count < 2
