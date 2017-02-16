module Ph88 where

import Data.Char
import Test.QuickCheck

stringCases :: String -> Gen String
stringCases = traverse (elements . sequence [toLower, toUpper])
