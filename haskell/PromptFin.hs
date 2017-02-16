module PromptFin where

import Control.Monad
import Data.ByteString
import Pipes
import Pipes.Safe
import qualified Pipes.Prelude as P
import System.IO

promptReadFile :: (MonadIO m, MonadSafe m)
               => FilePath -> Producer ByteString m ()
promptReadFile path =
    bracket (liftIO $ openFile path ReadMode) (liftIO . hClose) loop
  where
    loop h = do
        bs <- liftIO $ do
              bs <- hGet h 8192
              b <- hIsEOF h
              when b $ hClose h
              return bs
        yield bs

takeWhile' :: Monad m => (a -> Bool) -> Pipe a a m a
takeWhile' predicate = go
  where
    go = do
        a <- await
        if (predicate a)
            then do
                yield a
                go
            else return a

main :: IO ()
main = runEffect $ for (each [1..10] >-> (takeWhile' (<4) >>= yield >> cat)) $
        liftIO . Prelude.print
