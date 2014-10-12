{-# LANGUAGE OverloadedStrings #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module VectorTest where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid
import Data.Vector.Unboxed.Mutable as VM

import GHC.TypeLits
import Data.Singletons

data Vec :: Nat -> * -> * where
    Nil :: forall a. Vec 0 a
    Cons :: a -> Vec n a -> Vec (n + 1) a

data Bar = Bar

data Foo where
    Foo ::
      { fooElemCount :: Sing (n :: Nat) -- use natVal to get the number out
      , fooElems     :: Vec n Bar
      } -> Foo

main :: IO ()
main = do
    v <- VM.new 1024 :: IO (VM.IOVector Int)
    s <- foldM (\i x -> (+) <$> pure i <*> VM.read v x) 0 [0..1023]
    print s
