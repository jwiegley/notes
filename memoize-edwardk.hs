{-# LANGUAGE BangPatterns #-}

module Main where

import Control.Monad.Instances
import Data.List
import Data.Function (fix)

col :: (Int -> (Int,Integer)) -> Int -> (Int,Integer)
col mf 1 = (1,0)
col mf !n
  | mod n 2 == 0 = let (x,y) = mf (n `div` 2) in (x+1,y+1)
  | otherwise    = let (x,y) = mf (n * 3 + 1) in (x+1,y+1)

f_list :: [(Int,Integer)]
f_list = map (col faster_f) [0..]

faster_f :: Int -> (Int,Integer)
faster_f n = f_list !! n

data Tree a = Tree (Tree a) a (Tree a)
instance Functor Tree where
    fmap f (Tree l m r) = Tree (fmap f l) (f m) (fmap f r)

index :: Tree a -> Int -> a
index (Tree _ m _) 0 = m
index (Tree l _ r) n = case (n - 1) `divMod` 2 of
    (q,0) -> index l q
    (q,1) -> index r q

nats :: Tree Int
nats = go 0 1
    where
        go !n !s = Tree (go l s') n (go r s')
            where
                l = n + s
                r = l + s
                s' = s * 2

toList :: Tree a -> [a]
toList as = map (index as) [0..]

f_tree :: Tree (Int,Integer)
f_tree = fmap (col fastest_f) nats

fastest_f :: Int -> (Int,Integer)
fastest_f = index f_tree

collatz :: Int -> [(Int,Integer)]
collatz m = foldr (\n rest ->
                    let y@(_,x) = fastest_f n in x `seq` y:rest) [] [1..m]

solution :: (Int, Integer)
solution = foldl' (\acc@(lg,_) x@(dep,_) -> if dep > lg then x else acc)
                  (0,0) (collatz 999999)

main :: IO ()
main = print solution