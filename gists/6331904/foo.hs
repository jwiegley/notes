module Main where

data Foo = Foo | Bar

foo (id -> Foo) = undefined
foo (id -> Bar) = undefined

main = undefined
