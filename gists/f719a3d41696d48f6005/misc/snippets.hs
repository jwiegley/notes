module Snippets where

import Data.List
import Data.Char

splitWith :: (a -> Bool) -> [a] -> [[a]]
splitWith _ [] = []
splitWith f x = let (pre, suf) = break f x
                in pre : case suf of
                           (_:ys) -> splitWith f ys
                           _      -> []

splitString :: String -> String -> [String]
splitString = split' []
    where split' acc s str@(x:xs)
              | s `isPrefixOf` str = acc : split' [] s (drop (length s) str)
              | otherwise          = split' (acc ++ [x]) s xs
          split' acc _ [] = [acc]

pairs :: (Integral a) => [a] -> [(a, a)]
pairs = filter (odd . fst) . map fn . tails
    where fn (x:y:_) = (x,y)
          fn _       = (0, 0)

primes :: [Int] -> [Int]
primes = fn []
    where fn _ [] = []
          fn acc (y:ys)
              | y `dividesBy` acc = fn acc ys
              | otherwise         = y : fn (y:acc) ys

          dividesBy _ [] = False
          dividesBy x (y:ys)
              | y == 1         = False
              | x `mod` y == 0 = True
              | otherwise      = dividesBy x ys

palindrome :: String -> Bool
palindrome str = pal' "" (evenLen str)
                 . filter (\x -> isAlpha x || isDigit x)
                 . map toLower $ str
    where pal' s evenL rest@(x:xs)
              |     evenL && s == rest      = True
              | not evenL && s == tail rest = True
              | otherwise = pal' (x:s) evenL xs
          pal' _ _ [] = False
          evenLen s = (length s) `mod` 2 == 0
