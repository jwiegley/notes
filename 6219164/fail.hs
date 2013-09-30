{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import Control.Failure
import Control.Exception
import Data.Typeable

data MathError = MyDivideByZero deriving (Show, Typeable)

instance Exception MathError

safeDiv :: Failure MathError m => Int -> Int -> m Int
safeDiv _ 0 = failure MyDivideByZero
safeDiv x y = return $ x `div` y

main :: IO ()
main = do
    print $ (safeDiv 10 0 :: Maybe Int)
    print $ (safeDiv 10 0 :: Either MathError Int)
    x <- safeDiv 10 0 :: IO Int
    print x
