module ToHex where

import Data.Bits
import Data.Char
import Data.Word

toHex :: Int -> String
toHex !x = go False 60 x
  where
    go b !n !y | n < 0     = ""
               | otherwise =
                   let num = (shiftR y n .&. 0xf)
                   in if b || num > 0 || n == 0
                      then dig num : go True (n - 4) y
                      else go False (n - 4) y
    dig !n   | n < 10    = chr (48 + n)
             | otherwise = chr (87 + n)

fromHex :: [Word8] -> Int
fromHex = go 0 0 . reverse
  where
    go acc _ []     = acc
    go acc 0 (x:xs) = go (acc + digit x) 16 xs
    go acc n (x:xs) = go (acc + n * digit x) (n * 16) xs

    digit 48 = 0
    digit 49 = 1
    digit 50 = 2
    digit 51 = 3
    digit 52 = 4
    digit 53 = 5
    digit 54 = 6
    digit 55 = 7
    digit 56 = 8
    digit 57 = 9

    digit 65  = 10
    digit 97  = 10
    digit 66  = 11
    digit 98  = 11
    digit 67  = 12
    digit 99  = 12
    digit 68  = 13
    digit 100 = 13
    digit 69  = 14
    digit 101 = 14
    digit 70  = 15
    digit 102 = 15
