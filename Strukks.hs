module Strukks where

pooleks :: Integer -> (Integer, Integer)
pooleks a = let y | mod a 2 == 0 = a `div` 2
                  | otherwise    = (a-1) `div` 2
            in (y, y)
