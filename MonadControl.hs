{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module MonadControl where

import           Control.Concurrent
import           Control.Exception (Exception, SomeException)
import qualified Control.Exception as E
import           Control.Monad
import           Control.Monad.Base
import           Control.Monad.IO.Class
import           Control.Monad.Trans.State

class MonadBaseControl b m | m -> b where
    type StM m a :: *
    liftBaseWith :: ((forall x. (m x -> b (StM m x))) -> b (StM m a)) -> m a

instance MonadBase b m => MonadBaseControl b (StateT s m) where
    type StM (StateT s m) a = m (a, s)
    liftBaseWith f = StateT $ \s -> do
        m <- liftBase $ f $ \k -> return $ runStateT k s
        m' <- m
        return m'

liftBaseDiscard :: (MonadBaseControl b m, Monad b, Monad m)
                => (b () -> b a) -> m () -> m a
liftBaseDiscard f m =
    liftBaseWith $ \run -> run . return =<< f (run m >> return ())

catch :: (MonadBaseControl IO m, Exception e) => m a -> (e -> m a) -> m a
catch f c = liftBaseWith $ \run -> run f `E.catch` (run . c)

main :: IO ()
main = do
    flip evalStateT (10 :: Int) $ go False
    flip evalStateT (10 :: Int) $ do
        modify (+5)
        go True `catch` \e -> do
            liftIO $ putStrLn "In the exception handler, state is:"
            get >>= liftIO . print
            liftIO $ putStrLn $
                "Caught exception: " ++ show (e :: SomeException)

  where
    go abort = do
        liftIO $ putStrLn "In the outer transformer, the state is:"
        get >>= liftIO . print

        x <- liftBaseWith $ \run -> do
            putStrLn "Hello, I'm in the IO monad!"
            run $ inner abort

        _threadId <- liftBaseDiscard forkIO $ void $ inner abort

        liftIO $ putStrLn $ "Back outside with: " ++ show x
        get >>= liftIO . print

    inner abort = do
        liftIO $ putStrLn "In the inner transformer, the state is:"
        get >>= liftIO . print
        modify (+1)
        when abort $ liftIO $ E.throwIO (userError "Oops!")
        return (100 :: Int)