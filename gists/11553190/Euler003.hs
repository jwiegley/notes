module Euler003 where

import           Control.Monad
import           Data.List
import           Data.Vector.Unboxed (Vector, (//))
import qualified Data.Vector.Unboxed as V

-- | Problem 3
--
-- The prime factors of 13195 are 5, 7, 13 and 29.
--
-- What is the largest prime factor of the number 600851475143 ?
--
-- >>> euler003 13195
-- 29
-- >>> euler003 600851475143
-- 6857

sieve :: Int -> Vector Bool
sieve n = let vec = V.replicate (n+1) True
          in foldl' (\v x -> v // [ (y, False)
                                  | y <- [x*2,x*3..n]]) vec [2..n]

isqrt :: Integer -> Integer
isqrt = ceiling . sqrt . fromIntegral

divisibleBy :: Integer -> Integer -> Bool
divisibleBy n x = x > 1 && n `mod` x == 0

divisibleByAny :: Integer -> Integer -> Bool
divisibleByAny n y = any (y `divisibleBy`) [3..isqrt n]

primes :: [Integer]
primes = 2 : filter (not . join divisibleByAny) [3,5..]

euler003 :: Integer -> Integer
euler003 n = last $ filter (n `divisibleBy`) $
             takeWhile (\x -> x < isqrt n) primes
