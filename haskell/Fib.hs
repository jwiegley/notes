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

fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = fib (n - 2) + fib (n - 1)

fibList :: [Int]
fibList = go 0
  where
  go n = fib n : go (n + 1)

lazyDiv :: Integral a => a -> a -> a
lazyDiv _ 0 = 1 `div` 0
lazyDiv x y = x `div` y

f :: Int → Bool
f 0 = False
f 1 = True
f 2 = unsafePerformIO pureEvil
f n = error "Oops"

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
