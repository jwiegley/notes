{-# LANGUAGE GADTs #-}

module SAT where

import Control.Applicative
import Test.QuickCheck

prop_distr :: (Applicative f, Alternative f,
              Arbitrary a, Arbitrary b,
              Eq (f b), f ~ [], a ~ Int, b ~ Int)
           => f a -> f a -> Bool
prop_distr x y = (f <*> (x <|> y)) == ((f <*> x) <|> (f <*> y))
  where
    f = [(+10), (+20), (+30), (+40)]

prop_distr' :: (Applicative f, Alternative f,
               Arbitrary a, Arbitrary b,
               Eq (f b), f ~ [], a ~ Int, b ~ Int)
            => f a -> Bool
prop_distr' x = ((f <|> g) <*> x) == ((f <*> x) <|> (g <*> x))
  where
    f = [(+10), (+20), (+30), (+40)]
    g = [(+50), (+60), (+70), (+80)]

rel :: Eq b => (a -> b) -> a -> b -> Bool
rel f x y = f x == y

h :: Int -> Int
h x = x * 3

h' :: Int -> Int -> Bool
h' = rel h

-- h' 3 9

-- data SAT a b =

-- Denotational Model for Satisfiability

-- We have a set of boolean variables.
-- We have a set of statements over those variables, giving True or False.
-- We have a boolean combination of such statements.

-- Conal style:

-- We have a set. Satisfiability is non-emptiness.
-- What algebraic abstractions do sets inhabit?

-- Mathematically, sets are:

--   Covariant Functor
--   Contravariant Functor
--   (Bivariant Functor)
--   Applicative
--   Monad
--   Monoid under both union (with empty set) and intersection
--   Semiring

-- Sets are not:

--   Group (though multisets with negative cardinalities are)

-- Multisets generalize into functions to semirings; so, instead of being
-- characterized as 'a -> Bool' as a Set might be, a Multiset is 'a -> Nat'.

-- (x₁ /\ x₂) \/ (!x₁ /\ !x₂)
-- atomic formulae are negated or non-negated projections of the variable

-- How is a function from a monoid to a semiring also a semiring, without
-- using the monoid? Then find another that does need the monoid. These two
-- should be different!
