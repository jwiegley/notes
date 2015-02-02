module Main where

import Control.Monad
import Control.Monad.CC
import Control.Monad.Free
import Control.Monad.IO.Class

data Step r m a f  = Step a (CCT r m f)
type Stepper r m a = Free (Step r m a) ()

cata :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
cata z _ (Pure a) = z a
cata z f (Free g) = f $ fmap (cata z f) g
{-# INLINE cata #-}

main :: IO ()
main = runCCT $ do
    Free (Step v k) <- reset $ \p -> do
        forM_ [1 :: Int,2,3,4,5] $ \val -> do
            liftIO $ putStrLn $ "val = " ++ show val
            shift p (\k -> return $ Free $ Step val (k $ return ()))
        return (Pure ())

    liftIO $ print v
    Free (Step v k) <- k
    liftIO $ print v
    Free (Step v k) <- k
    liftIO $ print v
    Free (Step v k) <- k
    liftIO $ print v
    Free (Step v k) <- k
    liftIO $ print v
    Pure () <- k
    return ()
