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

newtype Bar = Bar Int
    deriving Show

data Foo = Foo [Bar] [String]
    deriving Show

instance Reifies s Int => Arbitrary (Tagged s Bar) where
    arbitrary = return $ Tagged $ Bar $ reflect (Proxy :: Proxy s)

instance Reifies s (Int, Int) => Arbitrary (Tagged s Foo) where
    arbitrary = fmap Tagged $ do
        let (len, bar) = reflect (Proxy :: Proxy s)
        xs <- listOf (reify bar $ \(Proxy :: Proxy r) ->
                          unTagged <$> (arbitrary :: Gen (Tagged r Bar)))
        l  <- choose (1, len)
        ys <- vectorOf l (shuffle "Hello, world")
        return $ Foo xs ys

main :: IO ()
main = do
    [len, barValue] <- getArgs
    reify (read len :: Int, read barValue :: Int) $ \(Proxy :: Proxy s) ->
        print . unTagged =<< generate (arbitrary :: Gen (Tagged s Foo))
