{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Guarded where

import Data.Thyme
import Data.Thyme.Time
import UnliftIO
import UnliftIO.Concurrent

data GuardedOptions = GuardedOptions
  { goLogFunc        :: String -> IO ()
  , goPollWait       :: Int
  , goTotalTimeout   :: Int
  , goRefreshTimeout :: Int
  }

seconds :: Int -> Int
seconds = (* 1000000)

timed :: MonadUnliftIO m => m a -> m a
timed action = do
  mres <- timeout globalTimeout action
  case mres of
    Just x  -> pure x
    Nothing -> fail "Timed out"

polling :: MonadUnliftIO m => m (Maybe a) -> m (Maybe a)
polling action = do
  now <- liftIO getCurrentTime
  go now now
 where
  go t c | toMicroseconds (diffUTCTime c t) >= fromIntegral globalTimeout =
    return Nothing

  go t _ = do
    liftIO $ threadDelay globalPollWait
    action >>= \case
      Nothing -> go t =<< liftIO getCurrentTime
      Just x  -> return $ Just x

guardedAsync
  :: forall m a
   . MonadUnliftIO m
  => GuardedOptions
  -> (m () -> m a)
  -> m (Async a)
guardedAsync GuardedOptions {..} action = async $ mask $ \unmask -> do
  start <- liftIO getCurrentTime
  stamp <- liftIO $ newTVarIO start
  t     <- async $ action $ do
    now <- liftIO getCurrentTime
    atomically $ writeTVar stamp now
  unmask (watcher t start stamp) `catch` \(err :: SomeException) -> do
    liftIO $ goLogFunc $ "Caught exception in watcher: " ++ show err
    cancel t
    throwIO err
 where
  watcher :: Async a -> UTCTime -> TVar UTCTime -> m a
  watcher t start stamp = go
   where
    go = do
      liftIO $ threadDelay goPollWait
      eres <- poll t
      case eres of
        Just (Left err) -> do
          liftIO $ goLogFunc $ "Caught exception in thread: " ++ show err
          cancel t
          throwIO err
        Just (Right x) -> do
          liftIO $ goLogFunc "Guarded thread completed"
          pure x
        Nothing -> do
          now <- liftIO getCurrentTime
          if toMicroseconds (diffUTCTime now start)
             >= fromIntegral goTotalTimeout
          then
            fail "Thread reached total timeout"
          else
            do
              lastRefreshed <- liftIO $ readTVarIO stamp
              if toMicroseconds (diffUTCTime now lastRefreshed)
                   >= fromIntegral goRefreshTimeout
                then fail "Thread reached refresh timeout"
                else go

globalTimeout :: Int
globalTimeout = seconds 600

globalPollWait :: Int
globalPollWait = 200

async' :: MonadUnliftIO m => (String -> m ()) -> (m () -> m a) -> m (Async a)
async' logFunc action = do
  runInIO <- askUnliftIO
  guardedAsync
    GuardedOptions { goLogFunc        = unliftIO runInIO . logFunc
                   , goPollWait       = globalPollWait
                   , goTotalTimeout   = globalTimeout
                   , goRefreshTimeout = seconds 30
                   }
    action
