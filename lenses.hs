{-# LANGUAGE TemplateHaskell #-}

module Lenses where

import Control.Lens

data Foo = Foo { _counter :: Int } deriving Show

makeLenses ''Foo

main :: IO ()
main = do
  let x = Foo 10
      y = counter .~ ((x^.counter) + 1) $ x
  print y