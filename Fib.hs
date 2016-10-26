module Main where

import Control.Monad
import Data.Maybe
import Data.Time.Clock

fib :: Int -> IO Int
fib = fmap (fromMaybe 0) . go 0
  where
    go acc 0 = return $ Just acc
    go acc 1 = go (acc+1) 0
    go acc n = do
        t <- go acc (n-2)
        case t of
            Nothing -> return Nothing
            Just n' -> do
                t' <- go acc (n-1)
                return $ case t' of
                    Nothing  -> Nothing
                    Just n'' -> Just (n' + n'')

fibSlow :: Int -> IO Int
fibSlow = fmap (fromMaybe 0) . go 0
  where
    go acc 0 = return $ Just acc
    go acc 1 = go (acc+1) 0
    go acc n = do
        t <- go acc (n-2)
        fmap join $ forM t $ \n' -> do
            t' <- go acc (n-1)
            forM t' $ \n'' ->
                return (n' + n'')

main :: IO ()
main = test fib >> test fibSlow
  where
    test f = do
        t0 <- getCurrentTime
        n <- f 30
        print n
        t1 <- getCurrentTime
        print $ diffUTCTime t1 t0
