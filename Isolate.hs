module Isolate where

import Control.Monad
import Control.Monad.Loops
import Control.Monad.IO.Class
import Conduit

ioStuff :: [Int] -> IO String
ioStuff xs = do
  print xs
  return "Some relults I want to be able to go to a sink"

foo :: IO ()
foo = do
    xs <- yieldMany [1..10] $= go $$ sinkList
    print xs
  where
    go = void $ iterateUntil id $ takeExactlyC 2 $ do
        mx <- await
        case mx of
            Nothing -> return True
            Just x  -> do
                Just y  <- await
                yield $ x + y
                return False
