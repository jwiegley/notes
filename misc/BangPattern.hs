{-# LANGUAGE BangPatterns #-}

module Main where

a :: (Monad m) => Int -> m Int
a !x = return $! x + 1

sequence' :: Monad m => [m a] -> m [a]
sequence' = go []
  where
    go acc []     = return acc
    go acc (x:xs) = x >>= \v -> go (v:acc) xs

main :: IO ()
main = do
   let iternum = 1000000
   xs <- sequence' $ map (\i -> a (iternum-i)) [1..iternum]
   print xs
