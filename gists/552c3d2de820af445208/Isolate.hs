module Isolate where

import Control.Monad.Loops
import Control.Monad.IO.Class
import Conduit

main :: IO ()
main = yieldMany [1..10] $$ do
    _ <- iterateUntil null $ do
        xs <- takeExactlyC 2 sinkList
        liftIO $ print xs
        return xs
    return ()
