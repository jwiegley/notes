{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Mealy where

import           Control.DeepSeq
import           Control.Monad.Par (Par)
import qualified Control.Monad.Par as Par
import qualified Control.Monad.Par.Scheds.TraceInternal as Par
import           Data.ByteString
import           Data.Constraint
import           Data.Machine.MealyT
import           Text.Regex.PCRE.Heavy

class StateMachine k a b | k -> a, k -> b where
  type MStart k a b :: k
  type MTransition k a b (s :: k) (e :: k) :: Constraint

  data MState k a b :: k -> *
  machineNew  :: MState k a b (MStart k a b)
  machineDone :: MState k a b s -> Maybe b
  stepMachine
    :: a -> (forall e. MTransition k a b s e => MState k a b e -> r) -> MState k a b s -> r

-- | Every state machine instance can be represented as a Mealy machine.
mealy :: forall k a m b. (Monad m, Monoid b, StateMachine k a b) => MealyT m a b
mealy  = go $ machineNew @k
  where
  go :: forall s. MState k a b s -> MealyT m a b
  go st = MealyT $ \bs ->
    stepMachine
      bs
      (\st' -> case machineDone st' of
                  Just res -> pure (res, mempty)
                  Nothing  -> pure (mempty, go st'))
      st

-- | Parallel conjunctions of mealy machines.
put1 :: NFData a => Par.IVar (a, b) -> (a, b) -> Par ()
put1 v (a, b) = a `deepseq` b `seq` (Par.Par $ \c -> Par.Put v (a, b) (c ()))

spawn1 :: NFData a => Par (a, b) -> Par (Par.IVar (a, b))
spawn1 p = do
  r <- Par.new
  Par.fork (p >>= put1 r)
  return r

conj
  :: (Monoid b, NFData b) => MealyT Par a b -> MealyT Par a b -> MealyT Par a b
conj f g = MealyT $ \x -> do
  fx      <- spawn1 (runMealyT f x) -- start evaluating (f x)
  gx      <- spawn1 (runMealyT g x) -- start evaluating (g x)
  (a, f') <- Par.get fx             -- wait for fx
  (b, g') <- Par.get gx             -- wait for gx
  return (a <> b, f' <> g')          -- return results

{------------------------------------------------------------------------}

-- | Possible states the machine can be in.
data AMachineState
  = AMachineNew
  | AWaitingForFirst
  | AWaitingForSecond
  | AMachineFailed
  | AMachineDone

data MachineError = MachineError
  deriving Show

-- | All lawful transitions for this state machine.
type family MachineTransition s e :: Constraint where
  MachineTransition 'AMachineNew       'AWaitingForFirst  = ()
  MachineTransition 'AWaitingForFirst  'AWaitingForFirst  = ()
  MachineTransition 'AWaitingForFirst  'AWaitingForSecond = ()
  MachineTransition 'AWaitingForSecond 'AWaitingForSecond = ()
  MachineTransition 'AWaitingForSecond 'AMachineFailed    = ()
  MachineTransition 'AWaitingForSecond 'AMachineDone      = ()

instance StateMachine AMachineState ByteString [MachineError] where
  type MStart AMachineState ByteString [MachineError] = 'AMachineNew
  type MTransition AMachineState ByteString [MachineError] s e
    = MachineTransition s e

  data MState AMachineState ByteString [MachineError] :: AMachineState -> * where
    MachineNew
      :: MState AMachineState ByteString [MachineError] 'AMachineNew
    WaitingForFirst
      :: MState AMachineState ByteString [MachineError] 'AWaitingForFirst
    WaitingForSecond
      :: MState AMachineState ByteString [MachineError] 'AWaitingForSecond
    MachineFailed
      :: MachineError
      -> MState AMachineState ByteString [MachineError] 'AMachineFailed
    MachineDone
      :: MState AMachineState ByteString [MachineError] 'AMachineDone

  machineNew  = MachineNew
  machineDone = \case
    MachineFailed e -> Just [e]
    MachineDone     -> Just []
    _               -> Nothing

  -- | In 'stepMachine', the only language for talking about "what happens" is
  --   that of state transitions. An existential boxing of the result state is
  --   used to satisfy the type checker, and encapsulate a compile-time proof
  --   that the transition is lawful.
  stepMachine str k = \case
    MachineNew -> k WaitingForFirst

    WaitingForFirst ->
      if str =~ [re|foo|]
      then k WaitingForSecond
      else k WaitingForFirst

    WaitingForSecond ->
      if str =~ [re|quux|]
      then k $ MachineFailed MachineError
      else
        if str =~ [re|bar|]
        then k MachineDone
        else k WaitingForSecond

    MachineFailed e -> error $ "Cannot step a failed machine: " ++ show e
    MachineDone     -> error "Cannot step a done machine"
