{-# LANGUAGE GADTs #-}

module Hyper where

import Control.Arrow
import Control.Applicative
import Control.Category
import Control.Monad
import Data.Profunctor
import Prelude hiding (id, (.))

newtype Hyper a b = H { invoke :: Hyper b a -> b }

(#) :: Hyper b c -> Hyper a b -> Hyper a c
f # g = H (\k -> invoke f (g # k))

self :: Hyper a a
self = lift id

lift :: (a -> b) -> Hyper a b
lift f = f << lift f

(<<) :: (a -> b) -> Hyper a b -> Hyper a b
f << q = H (\k -> f (invoke k q))

base :: a -> Hyper b a
base = H . const

run :: Hyper a a -> a
run f = invoke f self

instance Category Hyper where
    id  = self
    (.) = (#)

instance Arrow Hyper where
    arr = lift

instance Profunctor Hyper where
    lmap f (H k) = H (k . rmap f)
    rmap f (H k) = H (f . k . lmap f)

instance Functor (Hyper a) where
    fmap = rmap

-- instance Monad (Hyper a) where
--     return    = base
--     H k >>= f = H $ \h -> invoke (f (k _)) h

-- instance Applicative (Hyper a) where
--     pure  = return
--     (<*>) = ap

fold :: [a] -> (a -> b -> c) -> c -> Hyper b c
fold [] _ n     = base n
fold (x:xs) c n = c x << fold xs c n

foldr' :: (b -> a -> a) -> a -> [b] -> a
foldr' c n xs = run (fold xs c n)

data Fold a b = forall x. Fold (x -> a -> x) x (x -> b)

instance Functor (Fold a) where
    fmap f (Fold step begin done) = Fold step begin (f . done)

instance Applicative (Fold a) where
    pure b    = Fold (\() _ -> ()) () (\() -> b)
    (Fold stepL beginL doneL) <*> (Fold stepR beginR doneR) =
        let step (xL, xR) a = (stepL xL a, stepR xR a)
            begin = (beginL, beginR)
            done (xL, xR) = (doneL xL) (doneR xR)
        in  Fold step begin done

data Fold' a b = forall x. Fold' (x -> Either b (a -> x)) x

instance Functor (Fold' a) where
    fmap f (Fold' step begin) =
        Fold' (\x -> case step x of
                    Left b -> Left (f b)
                    Right k -> Right k) begin

instance Applicative (Fold' a) where
    pure b = Fold' (\() -> Left b) ()
    (Fold' stepL beginL) <*> (Fold' stepR beginR) =
        let step (xL, xR) =
                case (stepL xL, stepR xR) of
                    (Left f, Left x)   -> Left (f x)
                    (Left _, Right h)  -> Right (\a -> (undefined, h a))
                    (Right k, Left _)  -> Right (\a -> (k a, undefined))
                    (Right k, Right h) -> Right (k &&& h)
            begin = (beginL, beginR)
        in  Fold' step begin

data HMachine a b = forall x. Hide (x -> Either b (a -> b, x)) x

instance Functor (HMachine a) where
    fmap f (Hide step begin) =
        Hide (\x -> case step x of
                    Left b  -> Left (f b)
                    Right (k, x') -> Right (f . k, x')) begin

instance Applicative (HMachine a) where
    pure b = Hide (\() -> Left b) ()
    (Hide stepL beginL) <*> (Hide stepR beginR) =
        let step (xL, xR) =
                case (stepL xL, stepR xR) of
                    (Left f, Left x)   -> Left (f x)
                    (Left f, Right (h, x'))  -> Right (f . h, (undefined, x'))
                    (Right (_, x'), Left _)  -> Right (undefined, (x', undefined))
                    (Right (_, x), Right (_, x')) -> Right (undefined, (x, x'))
            begin = (beginL, beginR)
        in  Hide step begin

main :: IO ()
main = do
    let x = fold ([1..10] :: [Int]) (+) 0
    print (run (lmap (+100) x))
    print (run (rmap (+100) x))
