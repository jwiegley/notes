# Analysis: Parameterized Recursive Type Pattern for SymExpr

## Summary

**The parameterized recursive type pattern CANNOT work with hegg's type-indexed e-graphs due to a fundamental kind mismatch.**

The current two-type approach (SymExpr and SymExprF) is actually the correct design for hegg integration.

## Kind Analysis

### What hegg Requires

From `Data.Equality.Language.Indexed`:

```haskell
type LanguageI :: forall k. (k -> Type -> Type) -> Constraint
class ( forall dom. Traversable (l dom)
      , forall dom a. (SingI dom, Ord a) => Ord (l dom a)
      ) => LanguageI l
```

hegg expects: `l :: k -> Type -> Type`

When partially applied: `l dom :: Type -> Type`

The second parameter is for the **recursive position** (e.g., ClassId in the e-graph).

### What the Parameterized Recursive Pattern Gives

Proposed pattern:

```haskell
data SymExpr (t :: SymType) (r :: SymType -> Type) where
  Constant :: Double -> SymExpr TyDouble r
  Symbol :: forall t. String -> SymExpr t r
  (:+:) :: forall t. r t -> r t -> SymExpr t r
  (:*:) :: r TyDouble -> r TyDouble -> SymExpr TyDouble r
  (:/:) :: r TyDouble -> r TyDouble -> SymExpr TyDouble r
```

Kind: `SymExpr :: SymType -> (SymType -> Type) -> Type`

When partially applied: `SymExpr t :: (SymType -> Type) -> Type`

### The Fundamental Mismatch

```
hegg expects:       l dom :: Type -> Type
                               ↓
                           Takes Type (like ClassId)

Proposed SymExpr:   SymExpr t :: (SymType -> Type) -> Type
                                  ↓
                              Takes (SymType -> Type) (higher-kinded)
```

**These are incompatible!**

## Concrete Example of the Failure

With hegg's `addI` function:

```haskell
addI :: forall k a (l :: k -> Type -> Type) dom.
        (LanguageI l, SOrd k, AnalysisI a l, SingI dom)
     => l dom ClassId  -- Need to pass ClassId :: Type
     -> EGraphI a l
     -> (ClassId, EGraphI a l)
```

To use SymExpr with addI, we would need:

```haskell
-- What we want to write:
addI (Constant 42.0 :: SymExpr TyDouble ???)

-- But SymExpr TyDouble expects (SymType -> Type), not Type!
-- We cannot pass ClassId because:
--   SymExpr TyDouble ClassId  -- TYPE ERROR!
--   Kind mismatch: ClassId :: Type
--                  Expected: SymType -> Type
```

## Why SymExprF Works Correctly

Current design:

```haskell
data SymExprF (t :: SymType) r where
  ConstantF :: Double -> SymExprF TyDouble r
  -- ...
```

Kind: `SymExprF :: SymType -> Type -> Type`

This matches hegg's requirement exactly:
- `k = SymType`
- `l = SymExprF`
- `SymExprF :: SymType -> Type -> Type` ✓

Usage with hegg:

```haskell
-- This works!
addI (ConstantF 42.0 :: SymExprF TyDouble ClassId) egraph
```

## Why Two Types Are Necessary

### SymExpr - User-Facing Recursive Type
```haskell
data SymExpr (t :: SymType) where
  Constant :: Double -> SymExpr TyDouble
  (:+:) :: forall t. SymExpr t -> SymExpr t -> SymExpr t
  -- Direct recursion, convenient for users
```

### SymExprF - Base Functor for hegg
```haskell
data SymExprF (t :: SymType) r where
  ConstantF :: Double -> SymExprF TyDouble r
  (:++:) :: forall t r. r -> r -> SymExprF t r
  -- Parameterized recursion, works with hegg
```

The duplication is **necessary** because:
1. SymExpr provides ergonomic direct recursion for users
2. SymExprF provides the kind signature required by hegg
3. These requirements are fundamentally incompatible in a single type

## Alternative Considered: Flip Parameters?

Could we define:

```haskell
data SymExpr (r :: Type) (t :: SymType) where ...
```

Kind: `SymExpr :: Type -> SymType -> Type`

No! hegg expects `l :: k -> Type -> Type`, not `l :: Type -> k -> Type`.
The domain parameter must come first.

## Could We Eliminate SymExpr Instead?

Yes! We could use only SymExprF:

```haskell
-- Base functor (works with hegg)
data SymExprF (t :: SymType) r where ...

-- User-facing recursive type
type Expr t = Fix (SymExprF t)

-- hegg integration
instance LanguageI SymExprF where ...
```

This would eliminate SymExpr and keep only SymExprF. This is a different simplification than what was proposed, but it would actually work.

## Conclusion

The parameterized recursive type pattern with `r :: SymType -> Type` is **incompatible** with hegg's type-indexed e-graphs because:

1. hegg requires `l :: k -> Type -> Type` (first-order recursion)
2. The pattern requires `r :: SymType -> Type` (higher-kinded recursion)
3. These requirements cannot be reconciled

**Recommendation**: Keep the current two-type approach (SymExpr and SymExprF) as it correctly separates concerns:
- SymExpr for user-facing code
- SymExprF for hegg integration

Alternatively, eliminate SymExpr and use only `SymExprF` with `Fix` for recursion.
