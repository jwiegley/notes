{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Conal where

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as M

newtype Multiset a = Multiset { getMultiset :: Map a Int }

instance Ord a => Semigroup (Multiset a) where
    Multiset xs <> Multiset ys = Multiset (M.unionWith (+) xs ys)

instance Ord a => Monoid (Multiset a) where
    mempty = Multiset M.empty
    mappend = (<>)

majority :: forall a. Multiset a -> Maybe (a, Int)
majority (Multiset xs) = M.foldlWithKey' go Nothing xs
  where
    go :: Maybe (a, Int) -> a -> Int -> Maybe (a, Int)
    go Nothing a n = Just (a, n)
    go r@(Just (_, n')) a n
        | n > n' = Just (a, n)
        | otherwise = r

newtype LArrow a b = LArrow { getLArrow :: [a -> b] }

data Bounds = Bound
    { timeToWait       :: Double
    , requiredMajority :: Double
    }

-- a -> b                ideal arrow
-- LArrow a b            real arrow(s)
-- a -> Maybe b          model partial arrow

denote :: (Fractional r, Ord r, Ord b) => r -> LArrow a b -> (a -> Maybe b)
denote threshold (LArrow fs) a = do
    -- jww (2018-09-29): The mapping must be done in parallel across all
    -- machines.
    (b, n) <- majority (mconcat (map (count . ($ a)) fs))
    guard (fromIntegral n > threshold * fromIntegral (length fs))
    pure b
  where
    count :: b -> Multiset b
    count k = Multiset (M.singleton k 1)

newtype BArrow a b = BArrow { getBArrow :: [forall r. a -> (b -> r) -> r] }

byzantine :: Ord b => BArrow a b -> LArrow a b
byzantine (BArrow _fs) = undefined

machineA :: Int -> Int
machineA = \case
    0 -> 1
    1 -> 5
    2 -> 3
    _ -> (-1)

machineB :: Int -> Int
machineB = \case
    0 -> 1
    1 -> 6
    2 -> 3
    _ -> (-1)

machineC :: Int -> Int
machineC = \case
    0 -> 2
    1 -> 7
    2 -> 3
    _ -> (-1)

broadcast :: Int -> [Int]
broadcast n = [machineA n, machineB n, machineC n]

foo :: Int -> [Int]
foo = broadcast >=> broadcast

join :: [[a]] -> [a]
join = concat

join' :: [[a]] -> [a]
join' = concat
