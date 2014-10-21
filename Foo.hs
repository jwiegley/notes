{-# LANGUAGE Rank2Types, ImpredicativeTypes #-}
-- We need ImpredicativeTypes, but GHC 6.8 doesn't think it
-- has them.  The cabal file configures this in a compiler-dependent
-- way.
{-# OPTIONS_GHC -Wall #-}
----------------------------------------------------------------------
-- |
-- Module      :  FRP.Reactive.Internal.Serial
-- Copyright   :  (c) Conal Elliott 2008
-- License     :  GNU AGPLv3 (see COPYING)
-- 
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
-- 
-- Serialize actions.
----------------------------------------------------------------------

module FRP.Reactive.Internal.Serial
  ( Serial, makeSerial, locking
  ) where

import Control.Concurrent.MVar
import Control.Applicative((<$>))
import Control.Exception (bracket_)

-- | Serializer.  Turns actions into equivalent but serialized actions
newtype Serial = Serial (forall a. IO a -> IO a)

-- | Make a locking serializer
makeSerial :: IO Serial
makeSerial = locking <$> newEmptyMVar

-- | Make a locking serializer with a given lock
locking :: MVar () -> Serial
locking lock = Serial (bracket_ (putMVar lock ()) (takeMVar lock))
