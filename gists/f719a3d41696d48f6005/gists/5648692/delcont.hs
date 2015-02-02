module Main where

import Control.Monad
import Control.Monad.CC
import Control.Monad.IO.Class

data Stepper r m a = Step a (CCT r m (Stepper r m a)) | Done

main = runCCT $ do
    Step v k <- reset $ \p -> do
        forM_ [1,2,3,4,5] $ \val -> do
            liftIO $ putStrLn $ "val = " ++ show val
            shift p (\k -> return $ Step val (k $ return ()))
        return Done

    liftIO $ print v
    Step v k <- k
    liftIO $ print v
    Step v k <- k
    liftIO $ print v
    Step v k <- k
    liftIO $ print v
    Step v k <- k
    liftIO $ print v
