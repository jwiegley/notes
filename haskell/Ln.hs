module Ln where

import Data.Bits
import Data.Ratio

pow' :: Rational -> Rational -> Rational
pow' _ 0 = 1
pow' x 1 = x
pow' x y = x * pow' x (pred y)

exp' :: Rational -> Rational
exp' = pow' 2.71828182845904523536028747135266249775724709369995

ln' :: Rational -> Rational
ln' x =
  sum (map (\i -> f i (pow' (x - 1) (toRational i) / toRational i))
        ([1..100] :: [Int]))
  where
  f :: Int -> Rational -> Rational
  f i | even i = negate
      | otherwise = id

{-
log' :: Rational -> Rational -> Rational
log' b x = ln' x / ln' b

sqrt' :: Rational -> Rational
sqrt' x = pow' x (1 % 2)

lnInt' :: Integer -> Integer
lnInt' = uncurry (go 8) . shiftLeft 0
  where
  go :: Integer -> Integer -> Integer -> Integer
  go 0 _ n = n
  go i count n =
    let n' = shiftR (n * n + 32768) 16 in
    let count' = shiftL count 1 in
    go (pred i)
       (if (n' < 32768) then count' else succ count')
       (if (n' < 32768) then n' * 2 else n')

  shiftLeft c n | n >= 32768 = (c, n)
                | otherwise  = shiftLeft (succ c) (shiftL n 1)
-}
