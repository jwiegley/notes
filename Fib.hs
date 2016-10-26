module Main where

import Control.Monad
import Data.Time.Clock

foldl :: Monad m => (a -> Maybe ()) -> (b -> a -> b) -> b -> [a] -> m (Maybe b)
foldl _ _ z []     = return (Just z)
foldl b f z (x:xs) =
    fmap join $ forM (b x) $ \() ->
        Main.foldl b f (f z x) xs

foldl2 :: Monad m => (a -> Maybe ()) -> (b -> a -> b) -> b -> [a] -> m (Maybe b)
foldl2 _ _ z []     = return (Just z)
foldl2 b f z (x:xs) =
    case b x of
        Nothing -> return Nothing
        Just () -> Main.foldl2 b f (f z x) xs

main :: IO ()
main = test Main.foldl >> test Main.foldl2
  where
    test f = do
        t0 <- getCurrentTime
        n <- f (\x -> if x<10000000 then Just () else Nothing) (+)
                 (0 :: Int) ([1..100000000] :: [Int])
        print n
        t1 <- getCurrentTime
        print $ diffUTCTime t1 t0
