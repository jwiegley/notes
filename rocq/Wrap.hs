module Wrap where

import qualified Prelude

data Nat =
   O
 | S Nat

foo :: Nat -> Nat
foo = foo_

bar :: Nat -> Nat
bar =
  foo

data Instrument =
   I_foo Nat

wrap :: Instrument -> a1 -> a1
wrap = \x d -> unsafePerformIO (x <$ modifyIORef events (d:))

foo' :: Nat -> Nat
foo' n =
  n

foo_ :: Nat -> Nat
foo_ n =
  foo' (wrap (I_foo n) n)

