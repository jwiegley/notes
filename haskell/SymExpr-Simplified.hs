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

{-|
This module shows an ALTERNATIVE simplification: Keep only SymExprF
and eliminate the separate SymExpr type.

This approach:
- Uses only ONE type (SymExprF) instead of two
- Works correctly with hegg's type-indexed e-graphs
- Provides user-facing recursion via Fix
-}
module SymExprSimplified where

import Data.Kind (Type)

-- | Fixpoint combinator for recursive types
newtype Fix (f :: Type -> Type) = Fix {unFix :: f (Fix f)}

-- | Phantom types representing the type-level tags
data SymType = TyDouble | TyString
  deriving (Show)

--------------------------------------------------------------------------------
-- Single Unified Type (works with hegg)
--------------------------------------------------------------------------------

-- | Base functor for symbolic expressions
--
-- Kind: SymExprF :: SymType -> Type -> Type
--
-- This matches hegg's requirement for l :: k -> Type -> Type
data SymExprF (t :: SymType) r where
  ConstantF :: Double -> SymExprF 'TyDouble r
  SymbolF :: forall t r. String -> SymExprF t r
  (:+:) :: forall t r. r -> r -> SymExprF t r
  (:*:) :: r -> r -> SymExprF 'TyDouble r
  (:/:) :: r -> r -> SymExprF 'TyDouble r

deriving instance (Show r) => Show (SymExprF t r)
deriving instance Functor (SymExprF t)
deriving instance Foldable (SymExprF t)
deriving instance Traversable (SymExprF t)

--------------------------------------------------------------------------------
-- User-Facing Recursive Type
--------------------------------------------------------------------------------

-- | Fixed point of SymExprF - this is the recursive type for users
type Expr t = Fix (SymExprF t)

-- | Smart constructor for constants
constant :: Double -> Expr 'TyDouble
constant x = Fix (ConstantF x)

-- | Smart constructor for symbols
symbol :: String -> Expr t
symbol s = Fix (SymbolF s)

-- | Smart constructor for addition
(.+.) :: Expr t -> Expr t -> Expr t
x .+. y = Fix (x :+: y)

-- | Smart constructor for multiplication
(.*.) :: Expr 'TyDouble -> Expr 'TyDouble -> Expr 'TyDouble
x .*. y = Fix (x :*: y)

-- | Smart constructor for division
(./.) :: Expr 'TyDouble -> Expr 'TyDouble -> Expr 'TyDouble
x ./. y = Fix (x :/: y)

infixl 6 .+.
infixl 7 .*., ./.

--------------------------------------------------------------------------------
-- Example Usage
--------------------------------------------------------------------------------

-- | Example: 42.0
e1 :: Expr 'TyDouble
e1 = constant 42.0

-- | Example: x
e2 :: Expr 'TyDouble
e2 = symbol "x"

-- | Example: 5.0 + 3.0
e3 :: Expr 'TyDouble
e3 = constant 5.0 .+. constant 3.0

-- | Example: (x * 2.0) / 2.0
e4 :: Expr 'TyDouble
e4 = (symbol "x" .*. constant 2.0) ./. constant 2.0

-- | Example: ((10.0 * 2.0) + 5.0) / 3.0
e5 :: Expr 'TyDouble
e5 = ((constant 10.0 .*. constant 2.0) .+. constant 5.0) ./. constant 3.0

--------------------------------------------------------------------------------
-- Direct SymExprF Usage (for hegg integration)
--------------------------------------------------------------------------------

{-
For hegg, we can use SymExprF directly with ClassId:

  import Data.Equality.Graph.Indexed

  -- Create expression node
  let node = ConstantF 42.0 :: SymExprF TyDouble ClassId

  -- Add to e-graph
  let (cid, egraph') = addI node egraph

This works because:
  - SymExprF :: SymType -> Type -> Type
  - Matches hegg's l :: k -> Type -> Type
  - Can instantiate with ClassId :: Type ✓
-}

-- Example of what we'd write for hegg (pseudo-code):
-- expr :: SymExprF 'TyDouble ClassId
-- expr = ConstantF 42.0

--------------------------------------------------------------------------------
-- Comparison with Two-Type Approach
--------------------------------------------------------------------------------

{-
Original approach (two types):

  data SymExpr (t :: SymType) where
    Constant :: Double -> SymExpr TyDouble
    (:+:) :: SymExpr t -> SymExpr t -> SymExpr t
    ...

  data SymExprF (t :: SymType) r where
    ConstantF :: Double -> SymExprF TyDouble r
    (:++:) :: r -> r -> SymExprF t r
    ...

Pros:
  + SymExpr is convenient (direct recursion, no Fix wrapper)
  + Clear separation between user API and hegg integration

Cons:
  - Code duplication
  - Two types to maintain
  - Need conversion between them

Simplified approach (one type):

  data SymExprF (t :: SymType) r where ...
  type Expr t = Fix (SymExprF t)

Pros:
  + No code duplication
  + Single source of truth
  + Works with hegg directly
  + Works with recursion schemes

Cons:
  - Need to wrap/unwrap Fix
  - Smart constructors needed for ergonomics
  - Pattern matching is less convenient

Recommendation:
  If you primarily work with hegg: Use simplified approach
  If you need both user API and hegg: Keep two types
-}

--------------------------------------------------------------------------------
-- Ord Instance (needed for hegg)
--------------------------------------------------------------------------------

-- For hegg, we need Ord instances. With the simplified approach:

deriving instance Eq r => Eq (SymExprF t r)

instance Ord r => Ord (SymExprF t r) where
  compare (ConstantF x) (ConstantF y) = compare x y
  compare (ConstantF _) _ = LT
  compare _ (ConstantF _) = GT

  compare (SymbolF x) (SymbolF y) = compare x y
  compare (SymbolF _) _ = LT
  compare _ (SymbolF _) = GT

  compare (x1 :+: y1) (x2 :+: y2) = compare x1 x2 <> compare y1 y2
  compare (_ :+: _) _ = LT
  compare _ (_ :+: _) = GT

  compare (x1 :*: y1) (x2 :*: y2) = compare x1 x2 <> compare y1 y2
  compare (_ :*: _) _ = LT
  compare _ (_ :*: _) = GT

  compare (x1 :/: y1) (x2 :/: y2) = compare x1 x2 <> compare y1 y2

--------------------------------------------------------------------------------
-- Integration with hegg (pseudo-code)
--------------------------------------------------------------------------------

{-
To use with hegg's type-indexed e-graphs:

1. Define LanguageI instance:

   instance LanguageI SymExprF
   -- Derived automatically from Traversable and Ord instances!

2. Create e-graph:

   egraph :: EGraphI () SymExprF
   egraph = emptyEGraphI

3. Add expressions:

   let node1 = ConstantF 42.0 :: SymExprF TyDouble ClassId
       (id1, eg1) = addI node1 egraph

       node2 = SymbolF "x" :: SymExprF TyDouble ClassId
       (id2, eg2) = addI node2 eg1

       node3 = id2 :*: id1 :: SymExprF TyDouble ClassId
       (id3, eg3) = addI node3 eg2

4. Perform rewrites and equality saturation as usual

The key insight: We don't need SymExpr at all if we're primarily
working with hegg. SymExprF + Fix is sufficient for both purposes.
-}
