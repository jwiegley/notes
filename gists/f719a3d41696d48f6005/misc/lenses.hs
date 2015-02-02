{-# LANGUAGE TemplateHaskell #-}

module Lenses where

import Data.Data.Lens
import Control.Lens

testTheInt :: (Int -> Bool) -> (a,b,c) -> Bool
testTheInt pred tup = pred $ head $ (tup ^.. biplate :: [Int])

data Foo = Foo { _counter :: Int } deriving Show

makeLenses ''Foo

main :: IO ()
main = do
  let x = Foo 10
      y = counter .~ ((x^.counter) + 1) $ x
  print y