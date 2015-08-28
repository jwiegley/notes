{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}

module Coyid where

{-
  Strictness always bothers me a little, since it forces you to do
  things like fusion manually. This prohibits code reuse. I won't
  elaborate on this too much since there is already a great blog
  post about this:

  http://augustss.blogspot.co.uk/2011/05/more-points-for-lazy-evaluation-in.html

  Playing around with Coyoneda I realized that some of these issues
  can be worked around using the Coyoneda lemma.

  Coyoneda gives rise to a functor to any arbitraty `f` you feed it.
  Mapping over this simply composes all the functions you are mapping
  without applying them directly to the thing you have lifted giving
  you fusion for free! This can have drastic preformance benefits.
-}

-- Carries around an `f` and a function that is applied when
-- you use `lowerC`
data Coyoneda f a = forall b. Coyo (b -> a) (f b)

-- `Coyoneda` gives rise to a `Functor` for any `f`
instance Functor (Coyoneda f) where
  fmap g (Coyo k f) = Coyo (g . k) f

-- Take any `f` and lift it to a `Coyoneda`
liftC :: f a -> Coyoneda f a
liftC f = Coyo id f

-- Take a `Coyoneda` and lower it to an `f`, here `f`
-- needs to have a `Functor` instance.
lowerC :: Functor f => Coyoneda f a -> f a
lowerC (Coyo k f) = fmap k f

-- Transforms `f` to `g`. This is useful if `f` does not
-- have a `Functor` instance but `g` has.
transformC :: (forall b. f b -> g b) -> Coyoneda f a -> Coyoneda g a
transformC t (Coyo k f) = Coyo k (t f)

-- A list we are going to use to throw `map` at.
list :: [Integer]
list = [10..20]

-- Our favorite `fib` function. Lets be super slow here!
fib :: Integer -> Integer
fib 0 = 1
fib 1 = 1
fib n = fib (n - 1) + fib (n - 2)

-- Take some `f` with a `Functor` instance and do some mapping.
-- `List` and `Coyoneda` both have `Functor` instances so both
-- will work just fine here.
test :: Functor f => f Integer -> f Integer
test = fmap fib . fmap (*2)

-- Apply `test` to `list` and take 2 elements from the result.
-- This will take a lot of time since we are mapping over all
-- elements of `list`, keep in mind that `fib` is pretty darn slow.
slowtest :: [Integer]
slowtest = take 2 (test list)

-- Apply `test` to `list` and take 2 elements from the result.
-- Here we are wrapping `list` in `Coyoneda`.
-- We are not applying our functions to every element of `list`
-- here. This is one of the beauties of `Coyoneda`.
fasttest :: [Integer]
fasttest = take 2 $ fmap (test id) list

-- using slowtest
-- » time -p ./coyo
-- [10946, 28657]
-- real 11.35
-- user 11.34
-- sys 0.00
--
-- using fasttest
-- » time -p ./coyo
-- [10946, 28657]
-- real 0.00
-- user 0.00
-- sys 0.00
main :: IO ()
main =
  -- print slowtest
  print fasttest
