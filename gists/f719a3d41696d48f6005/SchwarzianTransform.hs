module SchwarzianTransform where

import Control.Exception
import Data.List
import Data.Ord
import Debug.Trace

-- | Sort a list using a key on each element.  This implements the
--   decorate-sort-undecorate paradigm, also called a Schwarzian transform.
sortByKey :: Ord b => (a -> b) -> [a] -> [a]
sortByKey f = map snd . sortBy (comparing fst) . map (\x -> (f x, x))

sortByKey' :: Ord b => (a -> b) -> [a] -> [a]
sortByKey' f = map snd . sortBy (comparing fst)
    . map (\x -> x `seq` let k = f x in k `seq` (k, x))

main = do
    putStrLn $ "main SchwarzianTransform.hs:18.."
    -- (print =<<) $ (try :: IO a -> IO (Either SomeException a)) $ return $
    --     sortByKey length [trace "1" [] :: [Int], trace "2" undefined, trace "3" []]
    putStrLn $ "main SchwarzianTransform.hs:21.."
    (print =<<) $ (try :: IO a -> IO (Either SomeException a)) $ return $
        sortByKey' length [trace "1" [] :: [Int], trace "2" undefined, trace "3" []]
    putStrLn $ "main SchwarzianTransform.hs:24.."

foo = foldr (\x rest -> x : dropWhile (== x) rest) [] [1,2,2,2,3,3,4]
