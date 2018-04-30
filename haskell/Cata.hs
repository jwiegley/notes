{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Cata where

import Data.Fix
import Data.Functor.Compose
import Data.Semigroup

type Alg f a = f a -> a

data Cata f a = forall x. Cata (f x -> x) (x -> a)

instance Functor (Cata f) where
    fmap f (Cata alg red) = Cata alg (f . red)

algComp :: Functor f => (f a -> a) -> (f b -> b) -> f (a, b) -> (a, b)
algComp f g x = (f (fmap fst x), g (fmap snd x))

instance Functor f => Applicative (Cata f) where
    pure x = Cata (const ()) (const x)
    Cata falg fred <*> Cata galg gred =
        Cata (algComp falg galg) (\(f, g) -> fred f (gred g))

runCata :: Functor f => Cata f a -> Fix f -> a
runCata (Cata alg red) f = red (cata alg f)

-- Monoid Algebra
--
--   Categories
--     Objects      : Monoid Algebra
--     Morphism     : Monoid Homomorphism
--     Initial      : Initial Monoid Algebra (ListF)
--                    Free Objects
--     Catamorphism : Any morphism from the initial algebra to another algebra
--     Terminal     : Final Monoid Coalgebra
--     Anamorphism  : Any morphism from another algebra to the final algebra

data ListF a r = Nil | Cons a r deriving Functor

type List a = Fix (ListF a)

-- This is just an F-Algebra -> Church encoder
listFold :: ListF a r -> (a -> r -> r) -> r -> r
listFold l step beg = phi l
  where
    phi = \case Nil -> beg; Cons x y -> step x y

sumList :: Num a => Alg (ListF a) a
sumList = \case Nil -> 0; Cons x y -> x + y

sumList' :: forall a. Num a => Alg (ListF a) a
sumList' l = listFold l (+) 0

lenList :: Alg (ListF a) Int
lenList = \case Nil -> 0; Cons _ r -> 1 + r

lenList' :: Alg (ListF a) Int
lenList' l = listFold l (const (1+)) 1

liftWithRed :: Alg f a -> (a -> b) -> Cata f b
liftWithRed = Cata

lift :: Alg f a -> Cata f a
lift = flip liftWithRed id

-- This type appears in the 'foldl' library on Hackage:
--   https://hackage.haskell.org/package/foldl-1.4.0/docs/src/Control.Foldl.html#Fold
data Fold a b = forall x. Fold (x -> a -> x) x (x -> b)

-- It's easy enough to apply to our fixed point, if we know its Church
-- encoding. Note that we can auto-generate these Church encoded
-- representations using Template Haskell, using my 'recursors' library:
--   https://hackage.haskell.org/package/recursors
foldList :: Fold a b -> List a -> b
foldList (Fold step beg red) = red . cata (\l -> listFold l (flip step) beg)

data NatF r = O | S r deriving Functor

type Nat = Fix NatF

-- If we don't know the Church encoding, we can still use a Fold by just
-- applying 'cata' as we normally would.
foldNat :: Fold () a -> Nat -> a
foldNat (Fold step beg red) = red . cata (\case O -> beg; S r -> step r ())

-- However, while this allows us to use composed Folds on known F-algebras, it
-- doesn't let us compose algorithms for any F-algebra the way Cata does.

-- In a sense, this is due to the same distinction as between Church and Scott
-- encodings: the Fold type has lost the knowledge of 'f' at each level of the
-- recursion, making selective decision making based on that information
-- impossible, whereas Cata depends on it.

-- newtype AlgHom f g = AlgHom (Alg f (Fix g))

-- -- f (Fix g) -> Fix g  ==>  g (Fix h) -> Fix h
-- compose :: (Functor f, Functor g)
--         => AlgHom g h -> AlgHom f g -> AlgHom f h
-- compose (AlgHom f) (AlgHom g) = AlgHom (_ (cata f . g))

data Nested (f :: * -> *) (fs :: [* -> *]) a where
    Layer  :: (forall r. f (Nested fs a) -> a) -> Nested f fs a

runNested :: Nested (f ': fs) a -> f (Nested fs a) -> Nested fs a
runNested (Layer phi) = phi

compose :: Functor f => (f a -> a) -> (g a -> a) -> f (g a) -> a
compose f g = f . fmap g

addLayer :: (forall r. f r -> r) -> Nested fs a -> Nested (f ': fs) a
addLayer phi Bottom      = Layer phi
addLayer phi (Layer psi) = Layer (phi . psi)

-- jww (2018-04-27): Do these combined transforms fuse into a single pass?

main :: IO ()
main = do
    let xs = Fix (Cons 10
                  (Fix (Cons 20
                        (Fix (Cons 30
                              (Fix Nil)))))) :: List Int

    print $ runCata ((,) <$> lift sumList <*> lift lenList) xs

    -- => (60,3) in a single pass over the list
