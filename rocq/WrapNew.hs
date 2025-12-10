module Wrap where

import qualified Prelude

import Data.Functor ((<$))
import Data.IORef (IORef, modifyIORef, newIORef)
import System.IO.Unsafe (unsafePerformIO)

events :: IORef [Instrument a]
events = unsafePerformIO (newIORef [])
{-# NOINLINE events #-}

data Nat =
   O
 | S Nat

foo :: Nat -> Nat
foo = foo_

bar :: Nat -> Nat
bar =
  foo

data Instrument a =
   I_foo Nat

wrap :: a1 -> (Instrument a1) -> a1
wrap = \x d -> unsafePerformIO (x <$ modifyIORef events (d:))

foo' :: Nat -> Nat
foo' n =
  n

foo_ :: Nat -> Nat
foo_ n =
  foo' (wrap n (I_foo n))

