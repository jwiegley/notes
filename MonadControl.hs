{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module MonadControl where

import           Control.Concurrent
import           Control.Exception (Exception, SomeException)
import qualified Control.Exception as E
import           Data.Monoid
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Cont
import           Control.Monad.Trans.State
import           Data.Conduit hiding (MonadBaseControl)
import           Data.Conduit.Internal hiding (await, transPipe)

class (Monad m, Monad b) => MonadBaseControl b m | m -> b where
    data StM m a :: *
    liftBaseWith :: ((m x -> b (StM m x)) -> b a) -> m a
    restoreM :: StM m a -> m a

instance MonadBaseControl IO IO where
    data StM IO a = IOStM { unIOStM :: a }
    liftBaseWith f = f $ liftM IOStM
    restoreM       = return . unIOStM
    {-# INLINE liftBaseWith #-}
    {-# INLINE restoreM #-}

instance MonadBaseControl b m => MonadBaseControl b (StateT s m) where
    data StM (StateT s m) a = StateTStM { unStateTStM :: StM m (a, s) }
    liftBaseWith f = StateT $ \s -> do
        x <- liftBaseWith $ \runInBase -> f $ \k ->
            liftM StateTStM $ runInBase $ runStateT k s
        return (x, s)
    restoreM (StateTStM m) = StateT $ \_ -> restoreM m
    {-# INLINE liftBaseWith #-}
    {-# INLINE restoreM #-}

-- instance MonadBaseControl b m => MonadBaseControl b (ContT r m) where
--     data StM (ContT r m) a = ContTStM { unContTStM :: StM m a }
--     liftBaseWith f = ContT $ \h -> do
--         x <- liftBaseWith $ \runInBase -> f $ \k ->
--             liftM ContTStM $ runInBase $ runContT k h
--         h x
--     restoreM (ContTStM m) = lift $ restoreM m
--     {-# INLINE liftBaseWith #-}
--     {-# INLINE restoreM #-}

-- instance MonadBaseControl b m => MonadBaseControl b (ConduitM i o m) where
--     data StM (ConduitM i o m) a =
--         ConduitMStM { unConduitMStM :: StM m (a, Pipe i i o () m a) }
--     liftBaseWith f = ConduitM $ do
--         x <- liftBaseWith $ \runInBase -> f $ \k ->
--             liftM ConduitMStM $ runInBase $ return (undefined, conduitToPipe k)
--         return x
--     restoreM (ConduitMStM p) = do
--         p' <- restoreM p
--         ConduitM (transPipe id p')
--     {-# INLINE liftBaseWith #-}
--     {-# INLINE restoreM #-}

control :: MonadBaseControl b m => ((m x -> b (StM m x)) -> b (StM m a)) -> m a
control = liftBaseWith >=> restoreM
{-# INLINE control #-}

liftBaseDiscard :: MonadBaseControl b m => (b () -> b a) -> m () -> m a
liftBaseDiscard f m =
    liftBaseWith $ \runInBase -> f $ runInBase m >> return ()
{-# INLINE liftBaseDiscard #-}

catch :: (MonadBaseControl IO m, Exception e) => m a -> (e -> m a) -> m a
catch f c = control $ \run -> run f `E.catch` (run . c)
{-# INLINE catch #-}

main :: IO ()
main = do
    flip evalStateT (10 :: Int) $ go False

    flip evalStateT (10 :: Int) $ do
        modify (+5)
        go False `catch` \e -> do
            liftIO $ putStrLn "In the exception handler, state is:"
            get >>= liftIO . print
            liftIO $ putStrLn $
                "Caught exception: " ++ show (e :: SomeException)

        go True `catch` \e -> do
            liftIO $ putStrLn "In the exception handler, state is:"
            get >>= liftIO . print
            liftIO $ putStrLn $
                "Caught exception: " ++ show (e :: SomeException)

    -- putStrLn "Testing ContT 1..."
    -- putStrLn "--------------------"
    -- flip runContT return $ go' False False

    -- putStrLn "Testing ContT 2..."
    -- putStrLn "--------------------"
    -- flip runContT return $ go' False True

    -- putStrLn "Testing ContT 3..."
    -- putStrLn "--------------------"
    -- flip runContT return $ do
    --     go' False False `catch` \e -> do
    --         liftIO $ putStrLn "In the exception handler"
    --         liftIO $ putStrLn $
    --             "Caught exception: " ++ show (e :: SomeException)

    --     go' True False `catch` \e -> do
    --         liftIO $ putStrLn "In the exception handler"
    --         liftIO $ putStrLn $
    --             "Caught exception: " ++ show (e :: SomeException)

  where
    go abort = do
        liftIO $ putStrLn "In the outer transformer, the state is:"
        get >>= liftIO . print

        x <- control $ \run -> do
            putStrLn "Hello, I'm in the IO monad!"
            run $ inner abort

        threadId <- liftBaseDiscard forkIO $ do
            liftIO $ putStrLn "Inside the thread, state is:"
            get >>= liftIO . print
            void $ inner abort
        liftIO $ putStrLn $ "Forked thread: " ++ show threadId
        liftIO $ threadDelay 100

        liftIO $ putStrLn $ "Back outside with: " ++ show x
        get >>= liftIO . print

    inner abort = do
        liftIO $ putStrLn "In the inner transformer, the state is:"
        get >>= liftIO . print
        modify (+1)
        when abort $ liftIO $ E.throwIO (userError "Oops!")
        return (100 :: Int)

    go' abort jump = do
        liftIO $ putStrLn "Hello, I'm in the ContT monad!"
        x <- callCC $ \k -> do
            liftIO $ putStrLn "Inside of callCC"
            control $ \run -> do
                putStrLn "Hello, I'm in the IO monad!"
                run $ inner' k abort jump

        -- threadId <- liftBaseDiscard forkIO $ do
        --     liftIO $ putStrLn "Inside the thread"
        --     void $ inner' return abort
        -- liftIO $ putStrLn $ "Forked thread: " ++ show threadId
        -- liftIO $ threadDelay 100

        liftIO $ putStrLn $ "Back outside with: " ++ show x
        liftIO $ putStrLn "Hello, I'm at the end of the ContT monad!"

    inner' k abort jump = do
        liftIO $ putStrLn "In the inner transformer"
        when abort $ liftIO $ E.throwIO (userError "Oops!")
        when jump $ void $ k (200 :: Int)
        return (100 :: Int)
