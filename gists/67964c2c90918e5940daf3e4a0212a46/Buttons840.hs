module Main(main) where

import Control.Concurrent (threadDelay)
import Control.Concurrent.Async
import Control.Concurrent.STM
import Control.Monad
import Pipes
import Pipes.Concurrent
import System.Random (randomRIO)

a :: Producer Int IO ()
a = each [1..10]

b :: Pipe Int Int IO ()
b = do
  chan <- liftIO newTChanIO
  out  <- liftIO newTChanIO
  _ <- liftIO $ async $ do
    threadDelay =<< randomRIO (1000, 10000000)
    x <- atomically $ readTChan chan
    atomically $ writeTChan out (x*2)
  forever $ do
    x <- await
    liftIO $ atomically $ writeTChan chan x
    z <- liftIO $ atomically $ readTChan out
    yield z

c :: Consumer Int IO ()
c = do
  x <- await
  lift $ print x
  c

main :: IO ()
main = do
  (output1, input1, seal1) <- spawn' unbounded
  (output2, input2, seal2) <- spawn' unbounded
  runEffect $ fromInput input1 >-> b >-> toOutput output2