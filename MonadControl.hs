{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module MonadControl where

import           Control.Exception (Exception, SomeException)
import qualified Control.Exception as E
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.State

class MonadBaseControl b m | m -> b where
    data StM m a :: *
    liftBaseWith :: ((m x -> b (StM m x)) -> b a) -> m a
    restoreM :: StM m a -> m a

instance MonadBaseControl IO IO where
    data StM IO a = IOStM { unIOStM :: a }
    liftBaseWith f = f $ liftM IOStM
    restoreM       = return . unIOStM
    {-# INLINE liftBaseWith #-}
    {-# INLINE restoreM #-}

instance (MonadBaseControl b m, Monad b, Monad m)
         => MonadBaseControl b (StateT s m) where
    data StM (StateT s m) a = StateTStM { unStateTStM :: StM m (a, s) }
    liftBaseWith f = StateT $ \s -> do
        x <- liftBaseWith $ \runInBase -> f $ \k ->
            liftM StateTStM $ runInBase $ runStateT k s
        return (x, s)
    restoreM (StateTStM m) = StateT $ \_ -> restoreM m
    {-# INLINE liftBaseWith #-}
    {-# INLINE restoreM #-}

control :: (MonadBaseControl b m, Monad m)
        => ((m x -> b (StM m x)) -> b (StM m a)) -> m a
control = liftBaseWith >=> restoreM
{-# INLINE control #-}

-- liftBaseDiscard :: (MonadBaseControl b m, Monad b)
--                 => (b () -> b a) -> m () -> m a
-- liftBaseDiscard f m = liftBaseWith $ \runInBase ->
--     f $ runInBase m >> return ()
-- {-# INLINE liftBaseDiscard #-}

catch :: (MonadBaseControl IO m, Monad m, Exception e)
      => m a -> (e -> m a) -> m a
catch f c = control $ \run -> run f `E.catch` (run . c)
{-# INLINE catch #-}

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

        x <- control $ \run -> do
            putStrLn "Hello, I'm in the IO monad!"
            run $ inner abort

        -- threadId <- liftBaseDiscard forkIO $ do
        --     liftIO $ putStrLn "Inside the thread, state is:"
        --     get >>= liftIO . print
        --     void $ inner abort
        -- liftIO $ putStrLn $ "Forked thread: " ++ show threadId
        -- liftIO $ threadDelay 100

        liftIO $ putStrLn $ "Back outside with: " ++ show x
        get >>= liftIO . print

    inner abort = do
        liftIO $ putStrLn "In the inner transformer, the state is:"
        get >>= liftIO . print
        modify (+1)
        when abort $ liftIO $ E.throwIO (userError "Oops!")
        return (100 :: Int)