# SymExpr Refactoring Analysis

This directory contains an analysis of refactoring the `SymExpr` type system to use a parameterized recursive type pattern and its implications for hegg integration.

## Files

### SymExpr.hs (Original)
The current implementation with two separate types:
- `SymExpr t` - Direct recursive GADT for user-facing code
- `SymExprF t r` - Base functor for hegg integration

**Location**: `/Users/johnw/src/notes/haskell/SymExpr.hs`

### SymExpr-Analysis.md (Analysis)
Detailed analysis of why the parameterized recursive type pattern is incompatible with hegg's type-indexed e-graphs.

**Key Finding**: The parameterized pattern uses higher-kinded recursion `r :: SymType -> Type`, while hegg requires first-order recursion `r :: Type`. This is a fundamental kind mismatch that cannot be reconciled.

**Location**: `/Users/johnw/src/notes/haskell/SymExpr-Analysis.md`

### SymExpr-Parameterized.hs (Demonstration)
Implementation of the parameterized recursive type pattern showing:
- How the pattern works for recursive types
- Why it's incompatible with hegg (kind mismatch)
- What would be required to bridge the gap (not practical)

**Location**: `/Users/johnw/src/notes/haskell/SymExpr-Parameterized.hs`

### SymExpr-Simplified.hs (Alternative)
Alternative simplification that DOES work with hegg:
- Keep only `SymExprF` (eliminates duplication)
- Use `Fix (SymExprF t)` for user-facing recursive type
- Works directly with hegg's type-indexed e-graphs

**Location**: `/Users/johnw/src/notes/haskell/SymExpr-Simplified.hs`

## Summary of Findings

### Question
Can we use a parameterized recursive type pattern to eliminate the separate `SymExprF` type?

### Answer
**No**, due to a fundamental kind mismatch:

```haskell
-- Proposed parameterized pattern
data SymExpr (t :: SymType) (r :: SymType -> Type) where ...
-- Kind: SymType -> (SymType -> Type) -> Type

-- What hegg requires
type LanguageI :: forall k. (k -> Type -> Type) -> Constraint
-- Needs: k -> Type -> Type
```

When partially applied:
- Parameterized SymExpr: `SymExpr t :: (SymType -> Type) -> Type`
- hegg requirement: `l dom :: Type -> Type`

The second parameter has different kinds:
- SymExpr expects: `SymType -> Type` (higher-kinded)
- hegg expects: `Type` (first-order)

### Why This Matters

hegg's `addI` function needs to instantiate the recursion parameter with `ClassId :: Type`:

```haskell
addI :: l dom ClassId -> EGraphI a l -> (ClassId, EGraphI a l)
```

With the parameterized pattern, we cannot pass `ClassId` because:
```haskell
SymExpr TyDouble ClassId  -- TYPE ERROR!
-- Kind mismatch: ClassId :: Type
--                Expected: SymType -> Type
```

## Recommendations

### Option 1: Keep Current Approach (Recommended for now)
Maintain both `SymExpr` and `SymExprF`:
- **Pros**: Clear separation, convenient user API
- **Cons**: Code duplication

### Option 2: Use Simplified Approach
Keep only `SymExprF` and use `Fix`:
- **Pros**: No duplication, works with hegg
- **Cons**: Less convenient for users (need smart constructors)

### Option 3: Hybrid Approach
- Keep `SymExprF` for hegg
- Provide type class for conversion between `SymExpr` and `Fix (SymExprF t)`
- Best of both worlds but more complexity

## Theoretical Extensions

### Could Defunctionalization Work?
Theoretically yes, but impractical:

```haskell
data RecParam = RecClassId | RecRec

type family InterpRec (p :: RecParam) (t :: SymType) :: Type where
  InterpRec RecClassId t = ClassId
  InterpRec RecRec t = Rec SymExpr t

data SymExprD (t :: SymType) (r :: RecParam) where
  ConstantD :: Double -> SymExprD TyDouble r
  (:+D:) :: InterpRec r t -> InterpRec r t -> SymExprD t r
```

**Problems**:
- Extremely complex
- Loses type inference
- Extensive boilerplate
- Doesn't provide real benefits

**Verdict**: Not worth it

## Conclusion

The parameterized recursive type pattern is elegant for certain use cases, but it's fundamentally incompatible with hegg's type-indexed interface. The mismatch is at the kind level and cannot be worked around without significant complexity that negates any benefits.

**Recommendation**: Either keep the current two-type approach or adopt the simplified single-type approach with `Fix`. Do not attempt the parameterized recursive pattern for hegg integration.

## Testing the Code

All demonstration files compile successfully:

```bash
cd /Users/johnw/src/notes/haskell

# Original (should compile)
ghc -fno-code SymExpr.hs

# Parameterized pattern (compiles, demonstrates incompatibility)
ghc -fno-code SymExpr-Parameterized.hs

# Simplified approach (compiles, works with hegg)
ghc -fno-code SymExpr-Simplified.hs
```
