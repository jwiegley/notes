{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Data.Proxy
import Data.Tagged
import Data.Reflection
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import System.Environment

data Foo = Foo [Int] [String]
    deriving Show

instance Reifies s Int => Arbitrary (Tagged s Foo) where
    arbitrary = fmap Tagged $ do
        xs  <- listOf chooseAny
        len <- choose (1, reflect (Proxy :: Proxy s))
        ys  <- vectorOf len (shuffle "Hello, world")
        return $ Foo xs ys

main :: IO ()
main = do
    [len] <- getArgs
    reify (read len :: Int) $ \(Proxy :: Proxy s) ->
        print . unTagged =<< generate (arbitrary :: Gen (Tagged s Foo))
