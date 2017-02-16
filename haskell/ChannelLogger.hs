{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module ChannelLogger where

import Control.Concurrent.STM
import Control.Concurrent.STM.TBChan
import Control.Exception.Lifted
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Logger
import Control.Monad.Loops
import Control.Monad.Trans.Control
import Prelude hiding (ioError)

withChannelLogger :: (MonadBaseControl IO m, MonadIO m)
                  => Int
                  -> LoggingT m a
                  -> LoggingT m a
withChannelLogger size action = LoggingT $ \logger -> do
    chan <- liftIO $ newTBChanIO size
    runLoggingT action (channelLogger chan logger) `onException` dumpLogs chan
  where
    channelLogger chan logger loc src lvl str = atomically $ do
        full <- isFullTBChan chan
        when full $ void $ readTBChan chan
        writeTBChan chan $ logger loc src lvl str

    dumpLogs chan = liftIO $
        sequence_ =<< atomically (untilM (readTBChan chan) (isEmptyTBChan chan))

main :: IO ()
main = do
    runStdoutLoggingT $ withChannelLogger 128 $ do
        $(logInfo) "Hello!"
        $(logInfo) "GoodBye!"

    runStdoutLoggingT $ withChannelLogger 128 $ do
        $(logInfo) "Hello!"
        $(logInfo) "GoodBye!"
        throwIO (userError "Foo")
