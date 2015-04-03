{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module MMonad where

import Control.Monad.Writer

type family MEmpty :: k
type family MAppend (x :: k) (y :: k) :: k

class MMonad (m :: k -> * -> *) where
    mreturn :: a -> m MEmpty a
    mjoin   :: m x (m y a) -> m (MAppend x y) a

data Level = Low | Medium | High

newtype Secure (l :: Level) a = Secure { getSecure :: a }
    deriving Show

type instance MEmpty = 'Low

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

-- Has no meaning at runtime
instance MMonad Secure where
    mreturn = Secure
    mjoin (Secure (Secure x)) = Secure x

-- This function needs authentication before performing declassification
declassify :: Secure l a -> Secure 'Low a
declassify = Secure . getSecure

high :: Secure 'High Int
high = Secure 10

low :: Secure 'Low Int
low = Secure 10

low_in_high :: Secure 'High (Secure 'Low Int)
low_in_high = Secure (Secure 10)

main = do
    print low_in_high
    print (mjoin low_in_high :: Secure 'High Int)
    print (declassify (mjoin low_in_high) :: Secure 'Low Int)
    print (mjoin low_in_high :: Secure 'Low Int)
