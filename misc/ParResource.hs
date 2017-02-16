module ParResource where

import Control.Monad.IO.Class
import Control.Monad.Trans.Resource
import Control.Concurrent.ParallelIO.Local

parResourceT :: [ResourceT IO a] -> ResourceT IO [a]
parResourceT xs = do
    is <- getInternalState
    liftIO $ withPool 16 $
        flip parallel (map (flip runInternalState is) xs)
