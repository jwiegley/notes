{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MMonad where

import Control.Applicative

type family MEmpty :: k
type family MAppend (x :: k) (y :: k) :: k

class MFunctor (m :: k -> * -> *) where
    mfmap :: (a -> b) -> m x a -> m x b

class MFunctor m => MApplicative (m :: k -> * -> *) where
    mpure  :: a -> m MEmpty a
    mapply :: m x (a -> b) -> m y a -> m (MAppend x y) b

class MApplicative m => MMonad (m :: k -> * -> *) where
    mjoin   :: m x (m y a) -> m (MAppend x y) a

mreturn :: MMonad m => a -> m MEmpty a
mreturn = mpure

mbind :: MMonad m => m x a -> (a -> m y b) -> m (MAppend x y) b
mbind m f = mjoin (mfmap f m)

data Level = Low | Medium | High

newtype Secure (l :: k) a = Secure { getSecure :: a }
    deriving (Show, Functor)

instance Applicative (Secure l) where
    pure = Secure
    Secure f <*> Secure x = Secure (f x)

instance Monad (Secure l) where
    return = pure
    Secure m >>= f =
        let Secure x = f m in
        Secure x

type instance MEmpty = 'High

-- Define the join of the security semi-lattice
type instance MAppend 'Low    'Low    = 'Low
type instance MAppend 'Low    'Medium = 'Medium
type instance MAppend 'Low    'High   = 'High
type instance MAppend 'Medium 'Low    = 'Medium
type instance MAppend 'High   'Low    = 'High

type instance MAppend 'Medium 'Medium = 'Medium
type instance MAppend 'Medium 'High   = 'High
type instance MAppend 'High   'Medium = 'High

type instance MAppend 'High 'High = 'High

-- These instances have no computational content; the purpose of the
-- information flow analysis is that it happens at compile-time only.
instance MFunctor Secure where
    mfmap f (Secure x) = Secure (f x)

instance MApplicative Secure where
    mpure = Secure
    mapply (Secure f) (Secure x) = Secure (f x)

instance MMonad Secure where
    mjoin (Secure (Secure x)) = Secure x

-- TODO: Needs authentication before performing declassification
declassify :: Secure l a -> Secure 'Low a
declassify = Secure . getSecure

high :: Secure 'High Int
high = mpure 10

low :: Secure 'Low Int
low = declassify high

-- Any type may be used to provide classification, so long as the join is
-- defined in terms of the type-level monoid operations.

-- data AltLevel = Lowest | Highest

-- type instance MEmpty = 'Highest

-- declassifyest :: Secure l a -> Secure 'Lowest a
-- declassifyest = Secure . getSecure

-- lowest :: Secure 'Lowest Int
-- lowest = declassifyest (mpure 10)

main :: IO ()
main = print $ do
    let x :: Secure 'Low Int = declassify (mpure (+1)) <*> low
    -- If the 'High here is changed to 'Low, it is a type error
    (+) <$> high <*> x :: Secure 'High Int
  where
    (<$>) = mfmap
    (<*>) = mapply
    (>>=) = mbind
