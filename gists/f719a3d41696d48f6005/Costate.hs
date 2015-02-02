module Costate where

import Control.Comonad

newtype Costate s a = Costate (s, s -> a)
    deriving Functor

instance Comonad (Costate s) where
    extract (Costate (x, f)) = f x
    duplicate (Costate (x, f)) = Costate (x, \y -> Costate (y, f))

lens :: (s -> a) -> (s -> a -> s) -> s -> Costate a s
lens g p s = Costate (g s, p s)
