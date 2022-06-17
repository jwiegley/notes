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
import Control.Monad.Freer
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Control.Monad.ST
import Control.Monad.State.Class
import qualified Control.Monad.Trans.State as T
import Control.Monad.Except
import Data.Kind
import Data.Sum

data Capability c where
  Vanilla :: Eq c => c -> Capability c
  Managed :: Eq c => c -> r -> Capability c

-- This defines the type of the capability
data AllowEntry = AllowEntry {
  userId :: String
  }
  deriving Eq

data Transfer = Transfer {
  source :: String,
  target :: String
  }
  deriving Eq

data CapError
    = NotAllowed

-- This is the defcap "function", which may only be executed in the context of
-- a specific module "s".
allowEntry :: MonadError CapError m => AllowEntry -> m (Capability AllowEntry)
allowEntry c = pure $ Vanilla c

transfer :: MonadError CapError m => Transfer -> Int -> m (Capability Transfer)
transfer c amt = pure $ Managed c amt

type Capable cs v m =
  (MonadError CapError m, MonadState [Sum cs v] m)

extendState :: MonadState s m => (s -> s') -> (MonadState s' m => m a) -> m a
extendState f k = do
  s <- get
  -- x <- k (f s)
  x <- undefined
  pure x

withCapability
  :: forall c cs v m a. Capable cs v m
  => m (Capability c)
  -> Eff (Reader (Option (Capability c)) : cs) a
  -> Eff effs a
withCapability getC k = do
  c <- getC
  extendState (inject (Const c) :) k

requireCapability
  :: forall c cs v m. (Const (Capability c) :< cs, Capable cs v m)
  => c
  -> m ()
requireCapability c = do
  cs <- get
  forM_ cs $ \(c :: Sum cs v) ->
      case project c :: Maybe (Const (Capability c) v) of
          Just _ -> pure ()
          Nothing -> throwError NotAllowed

enter :: Const (Capability Transfer) :< cs => Capable cs v m => String -> m ()
enter userName = do
  withCapability (allowEntry AllowEntry { userId = userName }) $ do
    doEntry userName

doEntry
  :: (Const (Capability AllowEntry) :< cs,
     Const (Capability Transfer) :< cs,
     Capable cs v m)
  => String -> m ()
doEntry userName = do
  if userName == "john"
      then requireCapability AllowEntry {userId = userName}
      else requireCapability Transfer {source = "john", target = userName}
