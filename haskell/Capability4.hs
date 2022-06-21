{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Capability where

import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.Reader
import Control.Monad.Freer.State
import Data.Hashable
import Data.Foldable
import GHC.Generics
import Data.Map (Map)
import qualified Data.Map as M
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

{------------------------------------------------------------------------
 - PACT Types & Values
 ------------------------------------------------------------------------}

-- The type of Pact values
data PactTy
  = TUnit
  | TInt
  | TString
  | TPair PactTy PactTy
  deriving (Show, Eq)

-- Pact values, which internally have type PactTy
data PactValue
  = VUnit
  | VInt Int
  | VString String
  | VPair PactValue PactValue
  deriving (Show, Eq, Generic, Hashable)

-- Query whether a given value indeed has the desired type
hasType :: PactTy -> PactValue -> Bool
hasType TUnit VUnit = True
hasType TInt (VInt _) = True
hasType TString (VString _) = True
hasType (TPair a b) (VPair x y) = hasType a x && hasType b y
hasType _ _ = False

{------------------------------------------------------------------------
 - Capability types
 ------------------------------------------------------------------------}

-- The set of errors that might occur while using capabilities
data CapabilityError
  = UnknownCapability String
  | InvalidArgument PactTy PactValue
  | InvalidValue PactTy PactValue
  | CapabilityNotAvailable String PactValue
  | ManagedError String
  | TypeError

data Signature = Signature {
  argType :: PactTy,
  predicate :: forall effs. MonadCapability effs
    => PactValue -> Eff effs [Capability],
  managed :: Maybe (PactTy, PactValue -> EMealy PactValue)
  }

data ModuleDefs = ModuleDefs {
  capabilitySigs :: Map String Signature
}

-- A variant Mealy machine that goes from `a' to unit, but may yield an error.
newtype EMealy a = EMealy {
  runEMealy :: a -> Either CapabilityError (EMealy a)
  }

data Capability = Token String PactValue

-- Operations on the Pact database
data Database k v r where
  Read :: k -> (v -> r) -> Database k v r

type ManagedMap = HashMap (String, PactValue) (EMealy PactValue)

type MonadCapability effs =
  (Member (Error CapabilityError) effs,
   Member (Reader ModuleDefs) effs,
   Member (Reader [[Capability]]) effs,
   Member (State ManagedMap) effs,
   Member (Database String String) effs)

{------------------------------------------------------------------------
 - Capability functionality
 ------------------------------------------------------------------------}

lookupSignature :: forall effs. MonadCapability effs
  => String -> PactValue -> Eff effs Signature
lookupSignature name arg = do
  defs <- ask @ModuleDefs
  case M.lookup name (capabilitySigs defs) of
    Nothing -> throwError $ UnknownCapability name
    Just sig ->
      if hasType (argType sig) arg
      then pure sig
      else throwError $ InvalidArgument (argType sig) arg

-- Grant is also used to implement compose-capability
grant :: forall effs. MonadCapability effs
  => String -> PactValue -> Eff effs [Capability]
grant name arg = do
  sig <- lookupSignature @effs name arg
  predicate sig arg

checkCapability :: forall effs. MonadCapability effs
  => String -> PactValue -> Eff effs (Signature, Maybe Capability)
checkCapability name arg = do
  sig <- lookupSignature @effs name arg
  (sig,) . go <$> ask @[[Capability]]
 where
  go [] = Nothing
  go (caps : capss) = go' caps capss

  go' (tok@(Token cname carg) : _) _
    | name == cname && arg == carg = Just tok
  go' [] capss = go capss
  go' (_ : caps) capss = go' caps capss

installCapability :: forall effs. MonadCapability effs
  => String -> PactValue -> PactValue -> Eff effs ()
installCapability name arg val = do
  sig <- lookupSignature @effs name arg
  forM_ (managed sig) $ \(ty, mk) ->
    if hasType ty val
    then modify $ HM.insert (name, arg) (mk val)
    else throwError $ InvalidValue ty val

withCapability :: forall effs r. MonadCapability effs
  => String -> PactValue -> PactValue -> Eff effs r -> Eff effs r
withCapability name arg val action = do
  (sig, mcap) <- checkCapability @effs name arg
  case mcap of
    Nothing -> do
      forM_ (managed sig) $ \(ty, _) ->
        if hasType ty val
        then do
          mres <- gets (HM.lookup (name, arg))
          forM_ mres $ \mach ->
            case runEMealy mach val of
              Left err -> throwError err
              Right machine' ->
                modify $ HM.insert (name, arg) machine'
        else throwError $ InvalidValue ty val
      caps <- grant name arg
      local @[[Capability]] (caps :) action
    Just _ -> action

requireCapability :: forall effs. MonadCapability effs
  => String -> PactValue -> Eff effs ()
requireCapability name arg = do
  (_, mcap) <- checkCapability @effs name arg
  case mcap of
    Nothing -> throwError $ CapabilityNotAvailable name arg
    Just _ -> pure ()

{------------------------------------------------------------------------
 - Capability environment
 ------------------------------------------------------------------------}

type CapabilityM a =
  Eff [Reader ModuleDefs,
       Reader [[Capability]],
       State ManagedMap,
       Error CapabilityError] a

runCapabilities
  :: ModuleDefs
  -> CapabilityM a
  -> Either CapabilityError a
runCapabilities defs action =
  run $ runError $ evalState mempty $ runReader [] $ runReader defs action

{------------------------------------------------------------------------
 - Examples
 ------------------------------------------------------------------------}

allowEntry :: Signature
allowEntry = Signature {
  argType = TString,
  predicate = predFunc,
  managed = Nothing
  }
 where
  predFunc :: forall effs. MonadCapability effs
    => PactValue -> Eff effs [Capability]
  predFunc userId = do
    caps <- grant "LOG" VUnit
    pure $ Token "ALLOW-ENTRY" userId : caps

transferCap :: Signature
transferCap = Signature {
  argType = TPair TString TString,
  predicate = predFunc,
  managed = Just (TInt, mkMachine)
  }
 where
  predFunc :: forall effs. MonadCapability effs
    => PactValue -> Eff effs [Capability]
  predFunc (VPair sender receiver) = do
    ds <- grant "DEBIT" sender
    cs <- grant "CREDIT" receiver
    pure $ Token "TRANSFER" (VPair sender receiver) : ds ++ cs
   where
  predFunc _ = throwError TypeError

  mkMachine :: PactValue -> EMealy PactValue
  mkMachine (VInt managed) = EMealy f
   where
    f (VInt requested) =
      if managed >= requested
      then Left $ ManagedError "Transfer quantity exhausted"
      else Right $ mkMachine (VInt (managed - requested))
    f _ = error "impossible"
  mkMachine _ = error "impossible"
