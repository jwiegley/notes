{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
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
import Control.Monad.ST
import Data.STRef
import Data.Map (Map)
import qualified Data.Map as M

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
  deriving (Show, Eq)

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
  valueType :: PactTy,
  predicate :: forall s effs. MonadCapability s effs
    => PactValue -> PactValue -> Eff effs [Capability s]
  }

data ModuleDefs = ModuleDefs {
  capabilitySigs :: Map String Signature
}

newtype MealyT a = MealyT {
  runMealyT :: a -> Either CapabilityError (MealyT a)
  }

data Capability s
  = Token String PactValue
  | Managed String PactValue (STRef s (MealyT PactValue))

-- Operations on the Pact database
data Database k v r where
  Read :: k -> (v -> r) -> Database k v r

type MonadCapability s effs =
  (Member (Error CapabilityError) effs,
   Member (Reader ModuleDefs) effs,
   Member (Reader [[Capability s]]) effs,
   Member (Database String String) effs,
   Member (ST s) effs)

{------------------------------------------------------------------------
 - Capability functionality
 ------------------------------------------------------------------------}

lookupSignature :: forall s effs. MonadCapability s effs
  => String -> PactValue -> PactValue -> Eff effs Signature
lookupSignature name arg val = do
  defs <- ask @ModuleDefs
  case M.lookup name (capabilitySigs defs) of
    Nothing -> throwError $ UnknownCapability name
    Just sig ->
      if hasType (argType sig) arg
      then
        if hasType (valueType sig) val
        then pure sig
        else throwError $ InvalidValue (argType sig) arg
      else throwError $ InvalidArgument (argType sig) arg

-- Grant is also used to implement compose-capability
grant :: forall s effs. MonadCapability s effs
  => String -> PactValue -> PactValue -> Eff effs [Capability s]
grant name arg val = do
  sig <- lookupSignature @s @effs name arg val
  predicate sig arg val

checkCapability :: forall s effs. MonadCapability s effs
  => String -> PactValue -> PactValue -> Eff effs (Maybe (Capability s))
checkCapability name arg val = do
  _ <- lookupSignature @s @effs name arg val
  capss <- ask @[[Capability s]]
  go capss
 where
  go [] = pure Nothing
  go (caps : capss) = go' caps capss

  go' (tok@(Token cname carg) : _) _ | name == cname && arg == carg =
    pure $ Just tok
  go' (mng@(Managed cname carg _) : _) _ | name == cname && arg == carg = do
    pure $ Just mng
  go' [] capss = go capss
  go' (_ : caps) capss = go' caps capss

withCapability :: forall s effs r. MonadCapability s effs
  => String -> PactValue -> PactValue -> Eff effs r -> Eff effs r
withCapability name arg val action = do
  mcap <- checkCapability @s @effs name arg val
  case mcap of
    Nothing -> do
      caps <- grant name arg val
      local @[[Capability s]] (caps :) action
    Just _ -> action

requireCapability :: forall s effs. MonadCapability s effs
  => String -> PactValue -> PactValue -> Eff effs ()
requireCapability name arg val = do
  mcap <- checkCapability @s @effs name arg val
  case mcap of
    Just (Managed _ _ ref) -> do
      machine <- send $ readSTRef ref
      case runMealyT machine val of
          Left err -> throwError err
          Right machine' -> send $ writeSTRef ref machine'
    Just _ -> pure ()
    Nothing -> throwError $ CapabilityNotAvailable name arg

{------------------------------------------------------------------------
 - Capability environment
 ------------------------------------------------------------------------}

type CapabilityM a =
  (forall s. Eff [Reader ModuleDefs,
             Reader [[Capability s]],
             Error CapabilityError,
             ST s] a)

runCapabilities
  :: ModuleDefs
  -> CapabilityM a
  -> Either CapabilityError a
runCapabilities defs action =
  runST $ runM $ runError $ runReader [] $ runReader defs action

{------------------------------------------------------------------------
 - Examples
 ------------------------------------------------------------------------}

allowEntry :: Signature
allowEntry = Signature {
  argType = TString,
  valueType = TUnit, -- stateless capability
  predicate = predFunc
  }
 where
  predFunc :: forall s effs. MonadCapability s effs
    => PactValue -> PactValue -> Eff effs [Capability s]
  predFunc userId VUnit = do
    caps <- grant "LOG" VUnit VUnit
    pure $ Token "ALLOW-ENTRY" userId : caps
  predFunc _ _ = throwError TypeError

transferCap :: Signature
transferCap = Signature {
  argType = TPair TString TString,
  valueType = TInt,
  predicate = predFunc
  }
 where
  predFunc :: forall s effs. MonadCapability s effs
    => PactValue -> PactValue -> Eff effs [Capability s]
  predFunc (VPair sender receiver) (VInt managed) = do
    ds <- grant "DEBIT" sender VUnit
    cs <- grant "CREDIT" receiver VUnit
    machine <- send $ newSTRef mkMachine
    pure $ Managed "TRANSFER" (VPair sender receiver) machine : ds ++ cs
   where
    mkMachine :: MealyT PactValue
    mkMachine = MealyT f
     where
      f (VInt requested) | managed >= requested =
        Left $ ManagedError "Transfer quantity exhausted"
      f _ = Right mkMachine
  predFunc _ _ = throwError TypeError
