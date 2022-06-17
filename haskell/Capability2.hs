{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Capability where

import Control.Applicative
import Control.Monad
import Data.Functor.Classes
import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.State
import Data.Sum

data Capability c = Capability c
  deriving Eq

data ManagedCapability c r = ManagedCapability c r (r -> r -> Either String r)

instance Eq c => Eq (ManagedCapability c r) where
  ManagedCapability l _ _ == ManagedCapability r _ _ = l == r

type Capable cs effs =
  (Member (State [Sum cs ()]) effs, Member (Error CapError) effs)

data CapError
    = NotAllowed
    | ManagedCapabilityFailure String

withCapability
  :: forall cs c effs a. (Member (Error CapError) effs,
                    Member (State [Sum cs ()]) effs,
                    Apply Eq1 cs,
                    Const (Capability c) :< cs)
  => Eff effs (Capability c)
  -> Eff effs a
  -> Eff effs a
withCapability getC k = do
  c <- getC
  cs <- get @[Sum cs ()]
  let injected = inject (Const c)
  if injected `elem` cs
    then k
    else do
      put (injected : cs)
      res <- k
      put cs
      pure res

withManagedCapability
  :: forall cs c r effs a. (Member (Error CapError) effs,
                      Member (State [Sum cs ()]) effs,
                      Apply Eq1 cs,
                      Const (ManagedCapability c r) :< cs)
  => Eff effs (ManagedCapability c r)
  -> Eff effs a
  -> Eff effs a
withManagedCapability getC k = do
  c <- getC
  cs <- get @[Sum cs ()]
  let injected = inject (Const c)
  if injected `elem` cs
    then k
    else do
      put (injected : cs)
      res <- k
      put cs
      pure res

requireCapability
  :: forall cs c effs. (Member (State [Sum cs ()]) effs,
                  Eq c, Const (Capability c) :< cs,
                  Member (Error CapError) effs)
  => c
  -> Eff effs ()
requireCapability cap = do
  cs <- get @[Sum cs ()]
  let res = flip map cs $ \c ->
          case project c :: Maybe (Const (Capability c) ()) of
              Just (Const (Capability c')) -> cap == c'
              Nothing -> False
  unless (any id res) $
    throwError NotAllowed

requireManagedCapability
  :: forall cs c r effs. (Member (State [Sum cs ()]) effs,
                    Eq c, Const (ManagedCapability c r) :< cs,
                    Member (Error CapError) effs)
  => c
  -> r
  -> Eff effs ()
requireManagedCapability cap req = do
  cs <- get @[Sum cs ()]
  let (cs', res) = unzip $ flip map cs $ \c ->
            case project c :: Maybe (Const (ManagedCapability c r) ()) of
                Just (Const (ManagedCapability c' n f)) ->
                  if cap == c'
                  then case f n req of
                    Left _ -> (c, False)
                    Right n' ->
                      (inject (Const (ManagedCapability c' n' f)), True)
                  else (c, False)
                Nothing -> (c, False)
  unless (any id res) $
    throwError NotAllowed
  put cs'

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

-- This defines the type of the capability
data AllowEntry = AllowEntry {
  userId :: String
  }
  deriving Eq

-- This is intended to be a "smart constructor". It should ideally hash the
-- data and sign it using a private key of the module that provides the
-- capability token, so that we can ensure upon requiring the capability that
-- it was granted by that module.
allowEntry :: Member (Error CapError) effs
  => AllowEntry -> Eff effs (Capability AllowEntry)
allowEntry c = pure $ Capability c

data Transfer = Transfer {
  source :: String,
  target :: String
  }
  deriving Eq

transfer :: Member (Error CapError) effs
  => Transfer -> Int -> Eff effs (ManagedCapability Transfer Int)
transfer c amt = pure $ ManagedCapability c amt $ \cur req ->
    if cur < req
    then Left "not enough funds"
    else Right (cur - req)

type ModuleCapabilities =
  '[Const (Capability AllowEntry),
    Const (ManagedCapability Transfer Int)]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

enter
  :: Capable ModuleCapabilities effs
  => String -> Eff effs ()
enter userName =
  withCapability @ModuleCapabilities
    (allowEntry AllowEntry { userId = userName }) $
    doEntry userName

doEntry
  :: Capable ModuleCapabilities effs
  => String -> Eff effs ()
doEntry userName =
  if userName == "john"
      then requireCapability @ModuleCapabilities
             AllowEntry {userId = userName}
      else requireManagedCapability @ModuleCapabilities
             Transfer {source = "john", target = userName} (100 :: Int)
