{-# LANGUAGE OverloadedStrings #-}

module AsyncC where

import qualified Conduit as C
import           Control.Applicative
import           Control.Concurrent.Async.Lifted
import           Control.Concurrent.Lifted hiding (yield)
import           Control.Concurrent.STM
import           Control.Exception
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Control
import           Control.Monad.Trans.Resource
import           Data.Conduit.Internal
import qualified Data.Conduit.List as C
import           Data.Maybe
import           Data.Monoid
import           Data.Void

asyncP :: (MonadBaseControl IO m, MonadResource m)
       => Pipe l i o u m r -> Pipe l i o u m ()
asyncP p = do
    var <- liftIO $ newTVarIO Nothing
    -- thread <- lift $ async $ runPipe $ gather var
    -- jww (2014-03-31): FIXME: Leaking the thread here on async exception
    addCleanup (const (cancel thread)) $ loop var
  where
    gather var = catchP (p >+> awaitAll var) $ \e ->
        liftIO $ atomically $
            writeTVar var (Just (Left (e :: SomeException)))
      where
        awaitAll var = do
            mx <- await
            liftIO $ atomically $ writeTVar var (Just (Right mx))
            case mx of
                Nothing -> return ()
                Just _  -> awaitAll var

    loop var = do
        eres <- liftIO $ atomically $ do
            mx <- readTVar var
            check $ isJust mx
            return mx
        case eres of
            Just (Left (e :: SomeException)) -> liftIO $ throwIO e
            Just (Right Nothing)  -> return ()
            Just (Right (Just x)) -> yield x >> loop var

asyncC :: (MonadBaseControl IO m, MonadResource m)
       => ConduitM i o m r
       -> ConduitM i o m ()
asyncC (ConduitM p) = ConduitM (asyncP p)

main :: IO ()
main = runResourceT $
    asyncC (C.sourceList [1..10]) C.$$ C.mapM_C (liftIO . print)
