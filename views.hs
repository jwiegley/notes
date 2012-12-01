{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UnicodeSyntax #-}

module Main where

import Control.Lens

data Foo = Foo String
         | Bar String

foo :: (Int,Foo) → IO ()
foo (view _2 → Foo x) = print ("a foo! " ++ show x)
foo (view _2 → Bar x) = print ("a bar: " ++ show x)
foo _ = print "dunno"

bar :: Maybe Int → IO ()
bar (Just ((+1) → 2)) = print "It's a 1"
bar _ = print "It's not"

baz ∷ Bool → (Bool → Maybe Bool) → Bool → Bool
baz α f (f → Just y) | Just z <- f α = z | otherwise = y

main :: IO ()
main = do
  foo (1,Foo "Hello")
  foo (1,Bar "World")
  bar (Just 1)
  print $ baz True Just False
