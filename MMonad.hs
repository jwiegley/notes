{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}

module MMonad where

import qualified Control.Applicative as Ap
import Prelude (Show, (.), ($), Int, IO, (+), print, error)
import qualified Prelude

type family MEmpty :: k
type family MAppend (x :: k) (y :: k) :: k

class MFunctor (m :: k -> * -> *) where
    mfmap :: (a -> b) -> m x a -> m x b

(<$>) :: MFunctor m => (a -> b) -> m x a -> m x b
(<$>) = mfmap

class MFunctor m => MApplicative (m :: k -> * -> *) where
    mpure  :: a -> m MEmpty a
    mapply :: m x (a -> b) -> m y a -> m (MAppend x y) b

(<*>) :: MApplicative m => m x (a -> b) -> m y a -> m (MAppend x y) b
(<*>) = mapply

class MApplicative m => MMonad (m :: k -> * -> *) where
    mjoin   :: m x (m y a) -> m (MAppend x y) a

mreturn :: MMonad m => a -> m MEmpty a
mreturn = mpure

mbind :: MMonad m => m x a -> (a -> m y b) -> m (MAppend x y) b
mbind m f = mjoin (mfmap f m)

(>>=) :: MMonad m => m x a -> (a -> m y b) -> m (MAppend x y) b
(>>=) = mbind

(>>) :: MMonad m => m x a -> m y b -> m (MAppend x y) b
x >> y = x >>= Prelude.const y

fail :: a
fail = error "whoops"

data Level = Low | Medium | High

newtype Secure (l :: Level) a = Secure { getSecure :: a }
    deriving (Show, Prelude.Functor)

instance Ap.Applicative (Secure l) where
    pure = Secure
    Secure f <*> Secure x = Secure (f x)

instance Prelude.Monad (Secure l) where
    return = Ap.pure
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
high = Secure 10

low :: Secure 'Low Int
low = declassify high

main :: IO ()
main = print $ do
    x <- declassify (mreturn (+1)) <*> high
    -- If the 'High here is changed to 'Low, it is a type error
    (+) <$> low <*> mpure x :: Secure 'High Int
