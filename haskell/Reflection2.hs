{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Data.Proxy
import Data.Reflection
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import System.Environment

data Foo s = Foo [Int] [String]
    deriving Show

instance Reifies s Int => Arbitrary (Foo s) where
    arbitrary = do
        xs  <- listOf chooseAny
        len <- choose (1, reflect (Proxy :: Proxy s))
        ys  <- vectorOf len (shuffle "Hello, world")
        return $ Foo xs ys

main :: IO ()
main = do
    [len] <- getArgs
    reify (read len :: Int) $ \(Proxy :: Proxy s) ->
        print =<< generate (arbitrary :: Gen (Foo s))
