-- This code was written by Ertugrul "ertes" Söylemez

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import Data.Monoid
import GHC.Exts


-- An existential field in a type requires pattern-matching clauses to
-- be universal in those fields.  That allows us to encode existentials
-- using CPS.
--
-- Existentials are only useful together either with a set of operations
-- or with a set of instances.  We can abstract over this choice via
-- using a generic structure parameter 'f':

newtype Exists f =
    Exists {
      element :: forall r. (forall a. f a -> r) -> r
    }

mapExists :: (forall a. f a -> g a) -> Exists f -> Exists g
mapExists f (Exists g) = g (\x -> exists (f x))

exists :: f a -> Exists f
exists x = Exists (\k -> k x)


-- This structure encodes an existential with one type class instance.
--
-- Unfortunately Haskell lacks the expressivity to encode multiple
-- instances right away, so if you need an arbitrary number of
-- instances, you need an indexed variant of this type, but that's
-- outside of the scope of this little demonstration:

newtype Given c a =
    Given {
      learn :: forall r. ((c a) => a -> r) -> r
    }

mapGiven :: ((c a) => a -> a) -> Given c a -> Given c a
mapGiven f gx = learn gx (\x -> teach (f x))

teach :: (c a) => a -> Given c a
teach x = Given (\k -> k x)


-- Here is a little example:

str1 :: Exists (Given Monoid)
str1 = exists (teach "abc")


-- We can manipulate the existing value using the extra knowledge that
-- it is a monoid:

str2 :: Exists (Given Monoid)
str2 = mapExists (mapGiven (\x -> x <> x)) str1
