{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

-- | * Introduction
--
--   Contains a combinator for concurrently joining a producer and a consumer,
--   such that the producer may continue to produce (up to the queue size) as
--   the consumer is concurrently consuming.
module Data.Conduit.Async ( buffer
                          , ($$&)
                          , bufferToFile
                          , gatherFrom
                          , drainTo
                          , main
                          ) where

import           Control.Applicative
import           Control.Concurrent.Async.Lifted
import           Control.Concurrent.STM
import           Control.Concurrent.STM.TBChan
import           Control.Exception.Lifted
import           Control.Monad hiding (forM_)
import           Control.Monad.IO.Class
import           Control.Monad.Loops
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Control
import           Data.Binary (Binary)
import qualified Data.Binary as Bin
import qualified Data.ByteString.Lazy as BL
import           Data.Conduit
import qualified Data.Conduit.List as CL
import           Data.Foldable (forM_)
import           System.Directory (removeFile)
import           System.IO

import           Data.Time

-- | Concurrently join the producer and consumer, using a bounded queue of the
--   given size.  The producer will block when the queue is full, if it is
--   producing faster than the consumers is taking from it.  Likewise, if the
--   consumer races ahead, it will block until more input is available.
--
--   Exceptions are properly managed and propagated between the two sides, so
--   the net effect should be equivalent to not using buffer at all, save for
--   the concurrent interleaving of effects.
buffer :: (MonadBaseControl IO m, MonadIO m)
       => Int -> Producer m a -> Consumer a m b -> m b
buffer size input output = do
    chan <- liftIO $ newTBQueueIO size
    control $ \runInIO ->
        withAsync (runInIO $ sender chan) $ \input' ->
            withAsync (runInIO $ recv chan $$ output) $ \output' -> do
                link2 input' output'
                wait output'
  where
    send chan = liftIO . atomically . writeTBQueue chan

    sender chan = do
        input $$ CL.mapM_ (send chan . Just)
        send chan Nothing

    recv chan = do
        mx <- liftIO $ atomically $ readTBQueue chan
        case mx of
            Nothing -> return ()
            Just x  -> yield x >> recv chan

-- | An operator form of 'buffer'.  In general you should be able to replace
--   any use of 'Data.Conduit.$$' with '$$&' and suddenly reap the benefit of
--   concurrency, if your conduits were spending time waiting on each other.
($$&) :: (MonadIO m, MonadBaseControl IO m)
      => Producer m a -> Consumer a m b -> m b
($$&) = buffer 64

data BufferContext a = BufferContext
    { chan      :: TBChan a
    , restore   :: TChan (IO [a])
    , slotsFree :: TVar (Maybe Int)
    , done      :: TVar Bool
    }

-- | Like 'buffer', except that when the bounded queue is overflowed, the
--   excess is cached in a local file so that consumption from upstream may
--   continue.  When the queue becomes exhausted by yielding, it is filled
--   from the cache until all elements have been yielded.
--
--   Note that the maximum amount of memory consumed is equal to memorySize *
--   3, so take this into account when picking a chunking size.
bufferToFile :: (MonadBaseControl IO m, MonadIO m, Binary a)
             => Int              -- ^ Size of the bounded queue in memory
             -> Maybe Int        -- ^ Max elements to keep on disk at one time
             -> FilePath         -- ^ Directory to write temp files to
             -> Producer m a
             -> Consumer a m b
             -> m b
bufferToFile memorySize fileMax tempDir input output = do
    context <- liftIO $ BufferContext
        <$> newTBChanIO memorySize
        <*> newTChanIO
        <*> newTVarIO fileMax
        <*> newTVarIO False
    control $ \runInIO ->
        withAsync (runInIO $ sender context) $ \input' ->
        withAsync (runInIO $ recv context $$ output) $ \output' -> do
            link2 input' output'
            wait output'
  where
    sender BufferContext {..} = do
        input $$ awaitForever $ \x -> liftIO $ join $ atomically $ do
            written <- tryWriteTBChan chan x
            if written
                then return $ return ()
                else do
                    action <- persistChan
                    writeTBChan chan x
                    return action
        liftIO $ atomically $ writeTVar done True
      where
        persistChan = do
            -- Empty the pending chan and return an action that writes the
            -- overflow to a disk file.
            xs <- exhaust chan
            mslots <- readTVar slotsFree
            let len = length xs
            forM_ mslots $ \slots -> check (len < slots)

            filePath <- newEmptyTMVar
            writeTChan restore $ do
                path <- atomically $ takeTMVar filePath
                bs <- BL.readFile path
                let xs'  = Bin.decode bs
                    len' = length xs'
                _ <- evaluate len'
                removeFile path
                atomically $ modifyTVar slotsFree (fmap (+ len'))
                return xs'

            case xs of
                [] -> return $ return ()
                _  -> do
                    modifyTVar slotsFree (fmap (+ (-len)))
                    return $ void $ async $ do
                        (path, h) <- openTempFile tempDir "restore.bin"
                        BL.hPut h $ Bin.encode xs
                        hClose h
                        atomically $ putTMVar filePath path

    recv context@(BufferContext {..}) = do
        (gather, exit) <- liftIO $ atomically $ do
            maction <- tryReadTChan restore
            case maction of
                Just action -> return (action, False)
                Nothing -> do
                    xs <- exhaustPoll chan
                    isDone <- readTVar done
                    return (return xs, isDone)
        mapM_ yield =<< liftIO gather
        unless exit $ recv context

    exhaustPoll chan = whileM (not <$> isEmptyTBChan chan) (readTBChan chan)
    exhaust chan     = untilM (readTBChan chan) (isEmptyTBChan chan)

-- | Gather output values asynchronously from an action in the base monad and
--   then yield them downstream.  This provides a means of working around the
--   restriction that 'ConduitM' cannot be an instance of 'MonadBaseControl'
--   in order to, for example, yield values from within a Haskell callback
--   function called from a C library.
gatherFrom :: (MonadIO m, MonadBaseControl IO m)
           => Int                -- ^ Size of the queue to create
           -> (TBQueue o -> m ()) -- ^ Action that generates output values
           -> Producer m o
gatherFrom size scatter = do
    chan   <- liftIO $ newTBQueueIO size
    worker <- lift $ async (scatter chan)
    lift . restoreM =<< gather worker chan
  where
    gather worker chan = do
        (xs, mres) <- liftIO $ atomically $ do
            xs <- whileM (not <$> isEmptyTBQueue chan) (readTBQueue chan)
            (xs,) <$> pollSTM worker
        Prelude.mapM_ yield xs
        case mres of
            Just (Left e)  -> liftIO $ throwIO (e :: SomeException)
            Just (Right r) -> return r
            Nothing        -> gather worker chan

-- | Drain input values into an asynchronous action in the base monad via a
--   bounded 'TBQueue'.  This is effectively the dual of 'gatherFrom'.
drainTo :: (MonadIO m, MonadBaseControl IO m)
        => Int                        -- ^ Size of the queue to create
        -> (TBQueue (Maybe i) -> m r)  -- ^ Action to consume input values
        -> Consumer i m r
drainTo size gather = do
    chan   <- liftIO $ newTBQueueIO size
    worker <- lift $ async (gather chan)
    lift . restoreM =<< scatter worker chan
  where
    scatter worker chan = do
        mval <- await
        (mx, action) <- liftIO $ atomically $ do
            mres <- pollSTM worker
            case mres of
                Just (Left e)  ->
                    return (Nothing, liftIO $ throwIO (e :: SomeException))
                Just (Right r) ->
                    return (Just r, return ())
                Nothing        -> do
                    writeTBQueue chan mval
                    return (Nothing, return ())
        action
        case mx of
            Just x  -> return x
            Nothing -> scatter worker chan

main :: IO ()
main = do
    putStrLn "Without a filesystem limit:"
    beg <- getCurrentTime
    replicateM_ 16 $ do
        results <- newTChanIO
        let input = [1 :: Int .. 1024]
        bufferToFile 4 Nothing "/Users/johnw/Downloads/temp"
            (CL.sourceList input)
            (CL.mapM_ (atomically . writeTChan results))
        xs <- atomically $ untilM (readTChan results) (isEmptyTChan results)
        print $ xs == input
    end <- getCurrentTime
    print $ diffUTCTime end beg

    putStrLn "With a filesystem limit:"
    beg <- getCurrentTime
    replicateM_ 16 $ do
        results <- newTChanIO
        let input = [1 :: Int .. 1024]
        bufferToFile 4 (Just 19) "/Users/johnw/Downloads/temp"
            (CL.sourceList input)
            (CL.mapM_ (atomically . writeTChan results))
        xs <- atomically $ untilM (readTChan results) (isEmptyTChan results)
        print $ xs == input
    end <- getCurrentTime
    print $ diffUTCTime end beg
