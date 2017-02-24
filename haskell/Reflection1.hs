module Main where

import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen

data Foo = Foo [Int] [String]
    deriving Show

instance Arbitrary Foo where
    arbitrary = do
        xs  <- listOf chooseAny
        len <- choose (1, 100)
        ys  <- vectorOf len (shuffle "Hello, world")
        return $ Foo xs ys

main :: IO ()
main = print =<< generate (arbitrary :: Gen Foo)
