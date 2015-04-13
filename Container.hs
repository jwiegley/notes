{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

module Container where

import Control.Applicative
import Control.Monad.State
import Data.Void
import GHC.TypeLits
import qualified Data.List

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
    Empty :: ListS  0 Void a
    Cons  :: Int -> (Fin (n + 1) -> a) -> ListS (n + 1) (Fin (n + 1)) a

list0 :: [a] -> ListS 0 Void a
list0 _ = Empty

listn :: [a] -> ListS (n + 1) (Fin (n + 1)) a
listn l = Cons (length l) (go l)
  where
    go :: [a] -> Fin m -> a
    go []      _     = error "Invalid list index"
    go (x:_)   F1    = x
    go (_:xs) (FS i) = go xs i

instance Functor (ListS s p) where
    fmap f Empty = Empty
    fmap f (Cons n x)  = Cons n (fmap f x)

instance Applicative (ListS s p) where
    pure = Cons 1 . pure :: a -> ListS 1 (Fin 1) a
    Empty <*> _ = Empty
    _ <*> Empty = Empty
    Cons nl f <*> Cons nr x =
        Cons (nl * nr) $ \i -> f (i `div` nr) (x (i `mod` nr))

instance Monad (ListS s p) where
    return = pure
    Empty >>= _ = Empty
    Cons n k >>= f =
        -- Call 'f' for each index, and conceptually concat the results
        let (cnt,res) =
                Data.List.foldl' (\(c,acc) i ->
                                   case f i of
                                       Empty -> (c,acc)
                                       Cons m h -> (c+m,acc)) (0,[]) [0..n] in
        -- A case cannot return results of variant types, even though the
        -- return type (ListS s p a) is polymorphic. This is typically
        -- overcome by switching to CPS argument passing, but we don't have
        -- that option in >>=.
        case cnt of
            0 -> Empty :: forall a. ListS 0 Void a
            -- use i to index into 'res', which should be a map of intervals
            -- to functions accepting an index from 0 to the size of that
            -- interval
            m -> Cons m $ \i -> undefined

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
