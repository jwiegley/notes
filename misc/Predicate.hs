-- Control.Conditional.Extras

{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ExistentialQuantification #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | 'Control.Conditional.Extras' provides a bit of extra stuff on top of
--   'Control.Conditional' (from the @cond@ package) for working with
--   truth-valued functions more abstractly.  It distinguishes between three
--   kinds of truth:
--
--      [@ToBool@] Where the answer is either yes or no.
--      [@ToMaybe@] Where the answer is yes or no, and yes carries a value.
--      [@ToEither@] Where the answer is yes or no, and both yes and no carry
--          meaning.
--
--    Generalized folds for each of these form the core of what this module
--    provides: 'bool', 'maybe', and 'either'.  You may also use the functions
--    'toBool', 'toMaybe' and 'toEither', to reify values with these
--    constraints.  'truth' and 'witness' are synonyms for the first two.
--
--    When creating your own instances, know that anything which is an
--    instance of 'ToEither' is automatically an instance of 'ToMaybe' and
--    'ToBool', and anything which is an instance of 'ToMaybe' is
--    automatically an instance of 'ToBool'.
--
--    Further, this module provides three type classes for working with
--    predicate function values: 'Predicate', 'MPredicate' and 'EPredicate'.
--    At the moment their own attraction is that they are instances of
--    'Contravariant'.  Use the functions 'test', 'mtest' and 'etest' to
--    extract the function.  Example: @test predicate truthValue@.
module Control.Conditional.Extras
       ( boolf, pand, por
       , ToMaybe(..), witness, maybe, fromMaybe, isJust, isNothing
       , ToEither(..), either
       , Predicate(..), test
       , MPredicate(..), mtest
       , EPredicate(..), etest
       , module Control.Conditional
       , module Data.Either
       , module Data.Maybe
       , module Data.Monoid
       ) where

import           Control.Conditional hiding ((??))
import           Data.Either hiding (either)
import           Data.Functor.Contravariant hiding (Predicate, getPredicate)
import           Data.Maybe hiding (maybe, fromMaybe, isJust, isNothing)
import           Data.Monoid
import qualified Prelude
import           Prelude hiding (maybe, either)

truth :: ToBool a => a -> Bool
truth = toBool

-- | 'boolf' is a higher-order form of 'bool'
boolf :: ToBool a => (x -> b) -> (x -> b) -> (x -> a) -> x -> b
boolf f g h x = if truth (h x) then f x else g x

pand :: (ToBool a, ToBool b) => a -> b -> Bool
pand (truth -> l) (truth -> r) = l && r

por :: (ToBool a, ToBool b) => a -> b -> Bool
por (truth -> l) (truth -> r) = l || r

instance ToBool Int where
    toBool = (==0)

instance ToBool Integer where
    toBool = (==0)

instance ToMaybe m => ToBool (m a) where
    toBool = isJust

class ToMaybe m where
    toMaybe :: m a -> Maybe a

maybe :: ToMaybe m => b -> (a -> b) -> m a -> b
maybe f t x = Prelude.maybe f t (witness x)

fromMaybe :: ToMaybe m => a -> m a -> a
fromMaybe _ (witness -> Just x) = x
fromMaybe f _ = f

isJust :: ToMaybe m => m a -> Bool
isJust = maybe False (const True)

isNothing :: ToMaybe m => m a -> Bool
isNothing = not . isJust

witness :: ToMaybe m => m a -> Maybe a
witness = toMaybe

instance ToMaybe Maybe where
    toMaybe = id

instance ToMaybe [] where
    toMaybe []    = Nothing
    toMaybe (x:_) = Just x

instance ToEither m => ToMaybe (m a) where
    toMaybe = either (const Nothing) Just

class ToEither e where
    toEither :: e a b -> Either a b

either :: ToEither e => (a -> c) -> (b -> c) -> e a b -> c
either f t e = Prelude.either f t (toEither e)

instance ToEither Either where
    toEither = id

data Predicate a = forall b. ToBool b => Predicate { getPredicate :: a -> b }

test :: Predicate a -> a -> Bool
test (Predicate f) x = truth (f x)

instance Contravariant Predicate where
    contramap f (Predicate g) = Predicate (g . f)

data MPredicate b a = forall m. ToMaybe m => MPredicate
    { getMPredicate :: a -> m b }

mtest :: MPredicate b a -> a -> Maybe b
mtest (MPredicate f) x = witness (f x)

instance Contravariant (MPredicate b) where
    contramap f (MPredicate g) = MPredicate (g . f)

data EPredicate b c a = forall m. ToEither m => EPredicate
    { getEPredicate :: a -> m b c }

etest :: EPredicate b c a -> a -> Either b c
etest (EPredicate f) x = toEither (f x)

instance Contravariant (EPredicate b c) where
    contramap f (EPredicate g) = EPredicate (g . f)

main :: IO ()
main = do
    print $ bool 0 1 True
    print $ bool 1 0 False
    print $ fromMaybe 1 Nothing
    print $ fromMaybe 0 (Just 1)
    print $ fromMaybe 1 []
    print $ fromMaybe 0 [1]
    print $ either id id (Left 1)
    print $ either id id (Right 1)
    print $ fromMaybe 1 (Left 10)
    print $ fromMaybe 0 (Right 1)
    print $ foo (Just 1) (Just 1)
    print $ if' (foo (Just 1) Nothing == 0) 1 0
    print $ bar (Predicate (const (Just 1)))
    print $ baz (MPredicate (const (Just 1)))
  where
    foo :: (ToBool a, ToBool b) => a -> b -> Int
    foo x y = bool 0 1 $ x `pand` y

    bar :: Predicate Int -> Int
    bar f = bool 0 1 $ test f 300

    baz :: MPredicate Int Int -> Int
    baz (MPredicate f) = bool 0 1 $ f 300
