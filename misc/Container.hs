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
import Data.List

-- In a dependently typed language, a container's accessor function's input
-- argument type is determined by its shape; in Haskell, we must use a GADT to
-- indicate each family of shapes by different constructors, so we can fix the
-- argument type using a type parameter.
--
-- What we lose is the common type 'Container P a'. Instead, our common
-- interface is Functor, which is mostly all that can be done with containers
-- in general.

-- data Fin :: Nat -> * where
--     F1 :: Fin (n + 1)
--     FS :: Fin n -> Fin (n + 1)

-- toFin :: Int -> Fin (n + 1)
-- toFin 0 = F1
-- toFin n = FS (toFin (n-1) :: Fin (n - 1 + 1))

-- instance Num (Fin n)
-- instance Eq (Fin n)
-- instance Ord (Fin n)
-- instance Real (Fin n)
-- instance Enum (Fin n)
-- instance Integral (Fin n)

-- List Container:
--   Shape : Set := Nat
--   Input : Shape -> Set := forall n : nat, Fin n
--   shape : Shape
--   accessor : Input shape -> a
--     Empty >> Input shape = Void, where shape = 0
--     Cons  >> Input shape = Fin (succ shape), where shape = succ shape
data ListS :: * -> * -> * where
    Empty :: ListS Void a
    Cons  :: Int -> (Int -> a) -> ListS Int a

list0 :: [a] -> ListS Void a
list0 _ = Empty

listn :: [a] -> ListS Int a
listn l = Cons (length l) (l !!)

instance Functor (ListS p) where
    fmap _ Empty = Empty
    fmap f (Cons n x) = Cons n (fmap f x)

instance Applicative (ListS p) where
    pure = undefined                    -- would require branching on p!
    Empty <*> _ = Empty
    _ <*> Empty = Empty
    Cons nl f <*> Cons nr x =
        Cons (nl * nr) $ \i -> f (i `div` nr) (x (i `mod` nr))

instance Monad (ListS p) where
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
            0 -> Empty
            -- use i to index into 'res', which should be a map of intervals
            -- to functions accepting an index from 0 to the size of that
            -- interval
            m -> Cons m $ \i -> undefined

-- State Container:
--   Shape : Set := ()
--   Input : Shape -> Set := fun _ => s
--   shape : Shape
--   accessor : Input shape -> a
--     HasState >> Input shape = s, where shape = ()
data StateS :: * -> * -> * where
    HasState :: (s -> a) -> StateS s a

instance Functor (StateS p) where
    fmap f (HasState x) = HasState (fmap f x)

state :: State s a -> StateS s a
state = HasState . evalState

class Container (p :: * -> * -> *) where
    getter :: p i a -> i -> a

instance Container ListS where
    getter Empty _ = error "Empty list"
    getter (Cons _ k) i = k i

instance Container StateS where
    getter (HasState k) = k

main :: IO ()
main = print $ getter (listn ([1,2,3,4,5] :: [Int])) 2
