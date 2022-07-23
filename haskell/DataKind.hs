{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Exp where

import Data.Kind

data PrimType =
  PrimUnit
  | PrimInteger
  | PrimDecimal
  | PrimTime
  | PrimBool
  | PrimString

data Ty =
  TyArrow Ty Ty
  | TyPrim PrimType
  | TySym
  | TyList Ty
  | TyPair Ty Ty
  | TyCap Ty Ty

data Var :: [Ty] -> Ty -> Type where
  ZV :: forall (ts :: [Ty]) (t :: Ty). Var (t : ts) t
  SV :: forall (ts :: [Ty]) (t :: Ty) (t' :: Ty). Var (t' : ts) t

data Exp :: [Ty] -> Ty -> Type where
  VAR :: forall (ts :: [Ty]) (t :: Ty). Var ts t -> Exp ts t
