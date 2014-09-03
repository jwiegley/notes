{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module NthFold where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Foldable
import Data.Monoid
import GHC.TypeLits

data Tree a = Nil | Box a | Pair (Tree a) (Tree a)
    deriving Foldable

get :: Int -> Tree a -> a
get n = either id (\_ -> error "not enough") . foldlM go n
  where
    go 0 x = Left x
    go p _ = Right (p - 1)

term = Pair (Pair (Box 0) (Box 10)) (Pair (Box 20) (Box 30))

summation :: (Num a) => Tree a -> a
summation = foldl' (+) 0

main = do
    print $ summation term
    print $ get 2 term -- should print 20
