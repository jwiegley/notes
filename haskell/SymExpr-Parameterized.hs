{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
This module demonstrates the parameterized recursive type pattern
and WHY it is incompatible with hegg's type-indexed e-graphs.

This is a DEMONSTRATION of what DOESN'T work, not production code.
-}
module SymExprParameterized where

import Data.Kind (Type)

-- | Phantom types representing the type-level tags
data SymType = TyDouble | TyString
  deriving (Show)

--------------------------------------------------------------------------------
-- Parameterized Recursive Type Pattern
--------------------------------------------------------------------------------

-- | Parameterized expression type with indexed recursion parameter
--
-- Kind: SymExpr :: SymType -> (SymType -> Type) -> Type
--
-- The second parameter 'r' has kind (SymType -> Type), which means
-- it's an indexed type constructor that, given a SymType, produces a Type.
data SymExpr (t :: SymType) (r :: SymType -> Type) where
  Constant :: Double -> SymExpr 'TyDouble r
  Symbol :: forall t r. String -> SymExpr t r
  (:+:) :: forall t r. r t -> r t -> SymExpr t r
  (:*:) :: r 'TyDouble -> r 'TyDouble -> SymExpr 'TyDouble r
  (:/:) :: r 'TyDouble -> r 'TyDouble -> SymExpr 'TyDouble r

deriving instance (forall t. Show (r t)) => Show (SymExpr t r)

-- | Recursive fixpoint for indexed functors
--
-- This takes a type constructor of kind (k -> (k -> Type) -> Type)
-- and ties the knot by passing itself as the recursion parameter.
newtype Rec (f :: k -> (k -> Type) -> Type) (t :: k) = Rec (f t (Rec f))

deriving instance (Show (f t (Rec f))) => Show (Rec f t)

-- | User-facing recursive expression type
type Expr t = Rec SymExpr t

-- | Constant functor for use with hegg
--
-- This wraps a value of type 'a' and ignores the index parameter.
-- Kind: Const :: Type -> SymType -> Type
newtype Const a (k :: SymType) = Const a
  deriving (Show, Eq, Ord)

--------------------------------------------------------------------------------
-- Example Usage (This part works fine)
--------------------------------------------------------------------------------

-- | Example: 42.0
exConst :: Expr 'TyDouble
exConst = Rec (Constant 42.0)

-- | Example: x
exSymbol :: Expr 'TyDouble
exSymbol = Rec (Symbol "x")

-- | Example: 5.0 + 3.0
exAdd :: Expr 'TyDouble
exAdd = Rec (Rec (Constant 5.0) :+: Rec (Constant 3.0))

-- | Example: (x * 2.0) / 2.0
exComplex :: Expr 'TyDouble
exComplex = Rec (Rec (Rec (Symbol "x") :*: Rec (Constant 2.0))
                 :/:  Rec (Constant 2.0))

--------------------------------------------------------------------------------
-- Why This DOESN'T Work with hegg
--------------------------------------------------------------------------------

{-
hegg expects a language with kind:  l :: k -> Type -> Type

For example:
  data SymExprF (t :: SymType) r where ...

Kind: SymExprF :: SymType -> Type -> Type

This can be used with hegg as:
  addI :: l dom ClassId -> EGraphI a l -> (ClassId, EGraphI a l)
  addI (ConstantF 42.0 :: SymExprF TyDouble ClassId) egraph

But with our parameterized SymExpr:

Kind: SymExpr :: SymType -> (SymType -> Type) -> Type

When we partially apply:
  SymExpr TyDouble :: (SymType -> Type) -> Type
                       ^^^^^^^^^^^^^^^^
                       This expects a type constructor!

We CANNOT pass ClassId because:
  - ClassId :: Type
  - But SymExpr TyDouble expects something of kind (SymType -> Type)

COMPILATION ERROR:
  addI (Constant 42.0 :: SymExpr TyDouble ClassId) egraph
                                           ^^^^^^^
  Kind mismatch:
    Expected: SymType -> Type
    Actual:   Type

The fundamental issue:
  - hegg uses FIRST-ORDER recursion (r :: Type)
  - This pattern uses HIGHER-KINDED recursion (r :: k -> Type)
  - These are incompatible!
-}

-- | This type alias shows what we'd WANT to write for hegg
--
-- But it won't compile because of the kind mismatch!
--
-- type HeggExpr t = SymExpr t ClassId  -- ERROR: Kind mismatch
--
-- We would need ClassId :: SymType -> Type, but ClassId :: Type

-- | To use Const as the recursion parameter (for hegg-style usage):
type FlatExpr t = SymExpr t (Const Int)

-- Example of using Const - note we must wrap the children!
exFlat :: FlatExpr 'TyDouble
exFlat = (Const 0 :: Const Int 'TyDouble) :+: (Const 1 :: Const Int 'TyDouble)

{-
This demonstrates that the pattern CAN work with an indexed recursion
parameter, but it CANNOT work with hegg because hegg needs the recursion
parameter to have kind Type, not (k -> Type).
-}

--------------------------------------------------------------------------------
-- What WOULD Work: Keep SymExprF Separate
--------------------------------------------------------------------------------

{-
The correct approach for hegg integration is to keep two types:

1. SymExprF for hegg (kind: SymType -> Type -> Type):

   data SymExprF (t :: SymType) r where
     ConstantF :: Double -> SymExprF TyDouble r
     (:++:) :: r -> r -> SymExprF t r
     ...

2. Either keep SymExpr for users, OR use Fix (SymExprF t):

   type Expr t = Fix (SymExprF t)

The parameterized recursive pattern is elegant for certain use cases,
but it's fundamentally incompatible with hegg's type-indexed interface
due to the kind mismatch between first-order and higher-kinded recursion.
-}

--------------------------------------------------------------------------------
-- Theoretical Fix: Defunctionalization
--------------------------------------------------------------------------------

{-
Could we use defunctionalization to bridge the gap? For example:

data RecParam = RecClassId | RecRec

type family InterpRec (p :: RecParam) (t :: SymType) :: Type where
  InterpRec RecClassId t = ClassId
  InterpRec RecRec t = Rec SymExpr t

data SymExprD (t :: SymType) (r :: RecParam) where
  ConstantD :: Double -> SymExprD TyDouble r
  (:+D:) :: InterpRec r t -> InterpRec r t -> SymExprD t r
  ...

This is theoretically possible but:
1. Extremely complex
2. Loses type inference
3. Requires extensive boilerplate
4. Still doesn't give us the benefits we want

Conclusion: Not worth it. Keep the two-type approach.
-}
