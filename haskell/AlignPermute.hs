{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module AlignPermute where

import Control.Monad
import Data.List (sort)
import Data.Align
import Data.These
import Text.Show.Pretty

subsequences :: [a] -> [[a]]
subsequences xs =  [] : nonEmptySubsequences xs

nonEmptySubsequences :: [a] -> [[a]]
nonEmptySubsequences []     = []
nonEmptySubsequences (x:xs) = [x] : foldr f [] (nonEmptySubsequences xs)
  where f ys r = ys : (x : ys) : r

possibilities :: [a] -> [b] -> [These a b]
possibilities xs ys =
    map This xs ++
    map (uncurry These) ((,) <$> xs <*> ys) ++
    map That ys

digits :: (a -> Int) -> (b -> Int) -> These a b -> [Int]
digits f g = \case
    This a    -> [f a]
    That b    -> [g b]
    These a b -> [f a, g b]

alignPermute :: forall a b. (a -> Int) -> (b -> Int) -> [a] -> [b]
             -> [[These a b]]
alignPermute f g xs ys = do
    path <- subsequences (possibilities xs ys)
    guard (sort (concatMap (digits f g) path) == coverage)
    return path
  where
    coverage = sort (map f xs ++ map g ys)

main :: IO ()
main = do
    pPrint $ alignPermute id id [1,2,3] [4,5]
