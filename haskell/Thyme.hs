module Thyme where

import Control.Concurrent (threadDelay)
import Control.Lens ((^.))
import Data.AffineSpace ((.-.))
import Data.Thyme (getCurrentTime, microseconds)

main :: IO ()
main = do
    now <- getCurrentTime
    threadDelay 100
    later <- getCurrentTime
    let msecs = (now .-. later) ^. microseconds
    print msecs
