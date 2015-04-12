{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Container where

import Control.Monad.State
import Data.Void
import GHC.TypeLits

-- In a dependently typed language, a container's accessor function's input
-- argument type is determined by its shape; in Haskell, we must use a GADT to
-- indicate each family of shapes by different constructors, so we can fix the
-- argument type using a type parameter.
--
-- What we lose is the common type 'Container P a'. Instead, our common
-- interface is Functor, which is mostly all that can be done with containers
-- in general.

data Fin :: Nat -> * where
    F1 :: Fin (n + 1)
    FS :: Fin n -> Fin (n + 1)

-- List Container:
--   Shape    : Set         := Nat
--   Input    : Shape -> Set := forall n : nat, Fin n
--   shape    : Shape
--   accessor : Input shape -> a
--     Empty >> Input shape = Void, where shape = 0
--     Cons  >> Input shape = Fin (succ shape), where shape = succ shape
data ListS :: Nat -> * -> * -> * where
    Empty :: (Void         -> a) -> ListS 0        Void           a
    Cons  :: (Fin (n + 1) -> a) -> ListS (n + 1) (Fin (n + 1)) a

list0 :: [a] -> ListS 0 Void a
list0 _ = Empty absurd

listn :: [a] -> ListS (n + 1) (Fin (n + 1)) a
listn l = Cons (go l)
  where
    go :: [a] -> Fin m -> a
    go []      _     = error "Invalid list index"
    go (x:_)   F1    = x
    go (_:xs) (FS i) = go xs i

instance Functor (ListS s p) where
    fmap f (Empty x) = Empty (fmap f x)
    fmap f (Cons x)  = Cons (fmap f x)

-- State Container:
--   Shape    : Set         := ()
--   Input    : Shape -> Set := fun _ => s
--   shape    : Shape
--   accessor : Input shape -> a
--     HasState >> Input shape = s, where shape = ()
data StateS :: () -> * -> * -> * where
    HasState :: (s -> a) -> StateS '() s a

instance Functor (StateS s p) where
    fmap f (HasState x) = HasState (fmap f x)

state :: State s a -> StateS '() s a
state k = HasState (evalState k)
