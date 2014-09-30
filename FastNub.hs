1module FastNub where

import Data.List (nub)
import Data.Set as Set
import Data.Time

fastNub :: Ord a => [a] -> [a]
fastNub = go Set.empty
  where
    go _ [] = []
    go m (y:ys)
        | Set.member y m = go m ys
        | otherwise      = y : go (Set.insert y m) ys

main :: IO ()
main = do
    start <- getCurrentTime
    print $ take 100 $ nub $ take 100000000 $ cycle [1,1,2,5,3,8,13,21,34]
    end <- getCurrentTime
    print $ diffUTCTime end start

    start <- getCurrentTime
    print $ take 100 $ fastNub $ take 100000000 $ cycle [1,1,2,5,3,8,13,21,34]
    end <- getCurrentTime
    print $ diffUTCTime end start
