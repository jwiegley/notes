module Ph88 where

import Data.Char
import Test.QuickCheck

stringCases :: String -> Gen String
stringCases [] = pure ""
stringCases (x:xs) = do
    x'  <- elements (toLower x:toUpper x:[])
    xs' <- stringCases xs
    return (x':xs')
