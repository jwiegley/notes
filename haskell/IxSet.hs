{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Data.List as List
import Data.Map.Internal (Map (..))
import qualified Data.Map.Internal as Map
import Data.Set (Set)
import qualified Data.Set as Set

fromList :: (Ord a, Ord k) => [(k, a)] -> Map k (Set a)
fromList xs =
  Map.fromListWith
    Set.union
    (List.map (\(k, v) -> (k, Set.singleton v)) xs)

delta, ratio :: Int
delta = 3
ratio = 2

size :: Map k a -> Int
size Tip = 0
size (Bin sz _ _ _ _) = sz
{-# INLINE size #-}

balanceR :: k -> a -> Map k a -> Map k a -> Map k a
balanceR k x l r = case l of
  Tip -> case r of
    Tip -> Bin 1 k x Tip Tip
    (Bin _ _ _ Tip Tip) ->
      Bin 2 k x Tip r
    (Bin _ rk rx Tip rr@(Bin _ _ _ _ _)) ->
      Bin 3 rk rx (Bin 1 k x Tip Tip) rr
    (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) ->
      Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
    (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _))
      | rls < ratio * rrs ->
          Bin (1 + rs) rk rx (Bin (1 + rls) k x Tip rl) rr
      | otherwise ->
          Bin
            (1 + rs)
            rlk
            rlx
            (Bin (1 + size rll) k x Tip rll)
            (Bin (1 + rrs + size rlr) rk rx rlr rr)
  (Bin ls _ _ _ _) -> case r of
    Tip -> Bin (1 + ls) k x l Tip
    (Bin rs rk rx rl rr)
      | rs > delta * ls -> case (rl, rr) of
          (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _)
            | rls < ratio * rrs ->
                Bin (1 + ls + rs) rk rx (Bin (1 + ls + rls) k x l rl) rr
            | otherwise ->
                Bin
                  (1 + ls + rs)
                  rlk
                  rlx
                  (Bin (1 + ls + size rll) k x l rll)
                  (Bin (1 + rrs + size rlr) rk rx rlr rr)
          (_, _) -> error "Failure in Data.Map.balanceR"
      | otherwise -> Bin (1 + ls + rs) k x l r

insertWith :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith = go
  where
    go :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
    go _ !kx x Tip = {-# SCC "Map.singleton" #-} Map.singleton kx x
    go f !kx x (Bin sy ky y l r) =
      case {-# SCC "compare" #-} compare kx ky of
        LT ->
          let z = {-# SCC "LT" #-} go f kx x l
           in {-# SCC "Map.balanceL" #-} Map.balanceL ky y z r
        GT ->
          let z = {-# SCC "GT" #-} go f kx x r
           in {-# SCC "Map.balanceR" #-} balanceR ky y l z
        EQ -> let !y' = f x y in Bin sy kx y' l r

fromList' :: forall a k. (Ord a, Ord k) => [(k, a)] -> Map k (Set a)
fromList' = go Map.empty
  where
    go :: Map k (Set a) -> [(k, a)] -> Map k (Set a)
    go m [] = m
    go m (!(k, v) : xs) =
      let !m' =
            {-# SCC "insertWith" #-}
            insertWith
              (\s s' -> {-# SCC "Set.union" #-} Set.union s s')
              k
              ({-# SCC "Set.singleton" #-} Set.singleton v)
              m
       in go m' xs

main :: IO ()
main = do
  let m :: Map Integer (Set Integer) =
        fromList' $ map (\x -> (x, x)) [1 .. 1_000_000]
  print $ Map.size m
