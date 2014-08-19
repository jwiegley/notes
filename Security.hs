{-# OPTIONS_GHC -fglasgow-exts #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Monad.Security
-- Copyright   :  (C) 2006 Edward Kmett
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (MPTC, FD)
--
-- A set of tools for building security monads.
-----------------------------------------------------------------------------

module Control.Monad.Security
    ( SecurityPolicy
    , SecurityLevel
    , SecurityLattice
    , witness
    , reclassify
    , supervise
    ) where

import Control.Monad
import Data.Type.Binary

-- | A `SecurityPolicy` is a particular relationship between a closed set of
--   `SecurityLevel`s.  The closure of this set is maintained by limiting the
--   export of the policy to the trusted code base.  A policy is a monad in
--   its own right, because to allow certain forms of lattice extensions later
--   we will want to be able to inject values into it.
class Monad p => SecurityPolicy p

-- | A `SecurityLevel` is a particular point inside our capability space. You
--   should not export the data constructors for your SecurityLevels, but only
--   export whatever methods you want to allow the end user to deconstruct
--   your secured data with including all access controls and permission
--   checks.
class (SecurityPolicy p, Monad l) => SecurityLevel p l | l -> p where
    supervise :: l a -> p a

-- | Note instances of this class must form a full meet-semilattice for
-- security purposes.
class ( SecurityLevel p l
      , SecurityLevel p l'
      , SecurityLevel p l''
      ) => SecurityLattice p l l' l'' | l l' -> l'', l -> p, l' -> p, l'' -> p
  where
    -- | witness is parameterized bind used in a more limited manner.
    witness :: l a -> (a -> l' b) -> l'' b

-- | @x & y = y iff x <= y@ is a meet semilattice law.
--
-- use this to raise the security level of a value using the supplied
-- `witness` for the `SecurityLattice` relationship
reclassify :: SecurityLattice p l m m => l a -> m a
reclassify x = witness x (return :: a -> m a)
