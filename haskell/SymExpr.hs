{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module SymExpr where

import Data.Kind (Type)

{-
This is the original type from the hegg library. The version of this
expression language given here is type-safe by using an index to express the
type of the expression.

data SymExpr a = Const Double
               | Symbol String
               | a :+: a
               | a :*: a
               | a :/: a
               deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
infix 6 :+:
infix 7 :*:, :/:

e1 :: Fix SymExpr
e1 = Fix (Fix (Fix (Symbol "x") :*: Fix (Const 2)) :/: (Fix (Const 2))) -- (x*2)/2
-}

-- | Fixpoint combinator for recursive types
newtype Fix (f :: Type -> Type) = Fix {unFix :: f (Fix f)}

-- | Phantom types representing the type-level tags
data SymType = TyDouble | TyString
  deriving (Show)

-- | GADT for symbolic expressions with type-level tracking
data SymExpr (t :: SymType) where
  Constant :: Double -> SymExpr TyDouble
  Symbol :: forall t. String -> SymExpr t
  (:+:) :: forall t. SymExpr t -> SymExpr t -> SymExpr t
  (:*:) :: SymExpr TyDouble -> SymExpr TyDouble -> SymExpr TyDouble
  (:/:) :: SymExpr TyDouble -> SymExpr TyDouble -> SymExpr TyDouble

deriving instance Show (SymExpr t)

-- | Base functor for SymExpr, suitable for use with Fix and recursion schemes
data SymExprF (t :: SymType) r where
  ConstantF :: Double -> SymExprF TyDouble r
  SymbolF :: forall t r. String -> SymExprF t r
  (:++:) :: forall t r. r -> r -> SymExprF t r
  (:**:) :: r -> r -> SymExprF TyDouble r
  (://:) :: r -> r -> SymExprF TyDouble r

deriving instance (Show r) => Show (SymExprF t r)

deriving instance Functor (SymExprF t)

deriving instance Foldable (SymExprF t)

deriving instance Traversable (SymExprF t)

-- | Fixed point of SymExprF
type Expr t = Fix (SymExprF t)

-- | Example expressions
e1 :: Expr TyDouble
e1 = Fix (Fix (ConstantF 10.0) :**: Fix (ConstantF 2.0)) -- 10 * 2

e2 :: Expr TyDouble
e2 = Fix (Fix (ConstantF 20.0) ://: Fix (ConstantF 2.0)) -- 20 / 2

e3 :: Expr TyDouble
e3 = Fix (Fix (ConstantF 5.0) :++: Fix (ConstantF 3.0)) -- 5 + 3

e4 :: Expr TyDouble
e4 = Fix (Fix (Fix (SymbolF "x") :**: Fix (ConstantF 2.0)) ://: Fix (ConstantF 2.0)) -- (x*2)/2
