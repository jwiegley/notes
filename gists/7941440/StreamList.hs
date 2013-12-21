{-# LANGUAGE NoImplicitPrelude #-}

module StreamList where

import Prelude (Int, Rational, (+), (/), (*))
import Control.Monad (join)
import Data.Function (($), (.))
import Data.List (repeat, head, map, tail, take)
import System.IO (print)

class Functor f where
    fmap :: (a -> b) -> f a -> f b

class Functor m => Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b

instance Functor [] where
    fmap _ [] = []
    fmap f (x:xs) = (f x: fmap f xs)

instance Monad [] where
    return = repeat
    xs >>= f = join (fmap f xs)
      where
        join :: [[a]] -> [a]
        join [] = []
        join ~(xs:xss) = head xs:join (map tail xss)

main = do
    print $ [1, 2, 3, 4] >>= (\x -> return [x,x,x])

    print $ take 10 $ (return 2 :: [Int])
    print $ take 10 $ (return 2 :: [Int]) >>= (return . (+1))
    print $ take 10 $ ([2] :: [Int]) >>= return
    print $ take 10 $ (([2,2,2] :: [Rational]) >>= (return . (/2)) >>= (return . (*2)))
    print $ take 10 $ ([2,2,2] :: [Rational]) >>= (\x -> return (x/2) >>= (return . (*2)))
