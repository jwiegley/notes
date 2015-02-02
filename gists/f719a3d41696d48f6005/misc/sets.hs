module Sets where

import Prelude hiding (elem)
import Control.Monad

type Set a = a -> Bool

isqrt :: Integer -> Integer
isqrt = ceiling . sqrt . fromIntegral

divisibleBy :: Integer -> Integer -> Bool
divisibleBy n x = x > 1 && n `mod` x == 0

divisibleByAny :: Integer -> Integer -> Bool
divisibleByAny n y = any (y `divisibleBy`) [3..isqrt n]

primeNumbers :: [Integer]
primeNumbers = 2 : filter (not . join divisibleByAny) [3,5..]

evens :: Integer -> Bool
evens = even

odds :: Integer -> Bool
odds = odd

primes :: Set Integer
primes x = x == head (dropWhile (<x) primeNumbers)

elem :: a -> Set a -> Bool
elem x s = s x

union :: Set a -> Set a -> Set a
union x y = \s -> x s || y s

intersect :: Set a -> Set a -> Set a
intersect x y = \s -> x s && y s

complement :: Set a -> Set a
complement x = \s -> not (x s)

empty :: b -> Bool
empty = const False

null :: Set a -> Bool
null = undefined

toList :: Set a -> [a]
toList = undefined

main :: IO ()
main = do
  print $ 5 `elem` evens
  print $ 6 `elem` evens
  print $ 5 `elem` (evens `union` odds)
  print $ 6 `elem` (evens `union` odds)
  print $ 5 `elem` (evens `intersect` odds)
  print $ 6 `elem` (evens `intersect` odds)
