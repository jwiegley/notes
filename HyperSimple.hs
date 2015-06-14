module Hyper where

import Control.Arrow
import Control.Category
import Prelude hiding (id, (.))

newtype Hyper a b = H { invoke :: Hyper b a -> b }

lift :: (a -> b) -> Hyper a b
lift f = f << lift f

base :: a -> Hyper b a
base = H . const

project :: Hyper a b -> a -> b
project q x = invoke q (base x)

(<<) :: (a -> b) -> Hyper a b -> Hyper a b
f << q = H (\k -> f (invoke k q))

(#) :: Hyper b c -> Hyper a b -> Hyper a c
f # g = H (\k -> invoke f (g # k))

self :: Hyper a a
self = lift id

instance Category Hyper where
    id  = self
    (.) = (#)

instance Arrow Hyper where
    arr    = lift
    first  = lift . first . project
    second = lift . second . project

main :: IO ()
main = do
    let f = ((+5) :: Int -> Int)
        g = ((\(x, y) -> (x+2,y+3)) :: (Int, Int) -> (Int,Int))
    print $ project (lift f) 6
    print $ project (first (lift f)) (6,6)
