{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- |
-- Module      : Singletons
-- Description : Real-world singleton pattern using singletons-th
--
-- THE KEY INSIGHT: Bridging Type-Level and Term-Level Programming
-- ================================================================
--
-- In Haskell, types are erased at runtime. When we write polymorphic code like:
--
--     foo :: forall a. SomeConstraint a => a -> String
--
-- We cannot pattern match on the type @a@ directly because types don't exist
-- at runtime. But what if we NEED to know which type we're dealing with to
-- perform type-specific logic?
--
-- This is where SINGLETONS come in:
--
-- 1. We define a type-level data kind (e.g., @LType = TInt | TBool | TFloat@)
-- 2. The singletons library creates a GADT singleton type that has exactly
--    ONE value per type (e.g., @STInt@ for @'TInt@, @STBool@ for @'TBool@)
-- 3. The @SingI@ type class provides the singleton value for each type
-- 4. At runtime, we can pattern match on the singleton to recover type information
--
-- This gives us:
--
-- * __Compile-time type safety__: Types prevent invalid operations
-- * __Runtime type dispatch__: We can choose behavior based on types
-- * __Type-driven computation__: Types compute other types via type families
--
-- The pattern in action:
--
-- @
-- serialize :: forall (a :: LType). SingI a => Foo a -> String
-- serialize foo = case sing @a of    -- Recover runtime type witness
--   STInt   -> "int:" ++ show foo    -- Type-specific behavior
--   STBool  -> "bool:" ++ show foo
--   STFloat -> "float:" ++ show foo
-- @
--
-- Real-world use cases:
--
-- * Type-safe DSLs (database queries, servant APIs)
-- * Dependent types in Haskell (length-indexed vectors, sized matrices)
-- * Generic serialization with type-specific formatting
-- * Resource management with type-level state machines
--
-- This module uses @singletons-th@ to auto-generate all the boilerplate.
-- The single TH splice @$(singletons [d| data LType = ... |])@ generates:
--
-- * Singleton type with @STInt@, @STBool@, @STFloat@ constructors
-- * @SingI@ instances for @'TInt@, @'TBool@, @'TFloat@
-- * @SingKind@ instance enabling @demote@/@toSing@ round-tripping
-- * Defunctionalization symbols for type-level programming
module Singletons where

import Data.Kind (Type)
import Data.Singletons.TH

-- | Type-level language type tags
-- The singletons TH splice generates everything we need!
$( singletons
     [d|
       data LType = TInt | TBool | TFloat
       |]
 )

deriving instance Show LType

deriving instance Eq LType

-- | A container that holds a value whose type is determined by the type parameter
data Foo (a :: LType) where
  FooInt :: Int -> Foo 'TInt
  FooBool :: Bool -> Foo 'TBool
  FooFloat :: Float -> Foo 'TFloat

instance Show (Foo a) where
  show = \case
    FooInt i -> show i
    FooBool b -> show b
    FooFloat f -> show f

-- | Existential wrapper - pairs a Foo with its singleton witness
data SomeFoo where
  SomeFoo :: (SingI a) => Foo a -> SomeFoo

-- | Show SomeFoo by discriminating on the singleton
instance Show SomeFoo where
  show (SomeFoo (foo :: Foo a)) = case sing @a of
    STInt -> show foo
    STBool -> show foo
    STFloat -> show foo

-- | Get the type name from a singleton witness
typeName :: forall (a :: LType). (SingI a) => String
typeName = case sing @a of
  STInt -> "Int"
  STBool -> "Bool"
  STFloat -> "Float"

-- | Serialize a Foo value to a tagged string
serialize :: forall (a :: LType). (SingI a) => Foo a -> String
serialize foo = case sing @a of
  STInt -> "int:" ++ show foo
  STBool -> "bool:" ++ show foo
  STFloat -> "float:" ++ show foo

-- | Parse a SomeFoo from a tagged string
parseSomeFoo :: String -> Either String SomeFoo
parseSomeFoo str = case break (== ':') str of
  ("int", ':' : rest) -> case reads rest of
    [(n, "")] -> Right $ SomeFoo (FooInt n)
    _ -> Left $ "Cannot parse '" ++ rest ++ "' as Int"
  ("bool", ':' : rest) -> case rest of
    "True" -> Right $ SomeFoo (FooBool True)
    "False" -> Right $ SomeFoo (FooBool False)
    _ -> Left $ "Cannot parse '" ++ rest ++ "' as Bool"
  ("float", ':' : rest) -> case reads rest of
    [(n, "")] -> Right $ SomeFoo (FooFloat n)
    _ -> Left $ "Cannot parse '" ++ rest ++ "' as Float"
  _ -> Left $ "Unknown format: " ++ str

-- | Demonstrate SingKind: demote a type-level value to term-level
showDemoted :: forall (a :: LType). (SingI a) => String
showDemoted = show (demote @a)

-- | Example usage
main :: IO ()
main = do
  putStrLn "=== Singleton Pattern with singletons-th ==="
  putStrLn ""

  let intFoo = FooInt 42
      boolFoo = FooBool True
      floatFoo = FooFloat 3.14

  putStrLn "1. Type names (via singleton, no value needed):"
  putStrLn $ "   " ++ typeName @'TInt
  putStrLn $ "   " ++ typeName @'TBool
  putStrLn $ "   " ++ typeName @'TFloat
  putStrLn ""

  putStrLn "2. Serialization:"
  putStrLn $ "   " ++ serialize intFoo
  putStrLn $ "   " ++ serialize boolFoo
  putStrLn $ "   " ++ serialize floatFoo
  putStrLn ""

  putStrLn "3. Existential wrapper (type erasure + recovery):"
  let existential = SomeFoo intFoo
  putStrLn $ "   SomeFoo (FooInt 42) = " ++ show existential
  putStrLn ""

  putStrLn "4. Parsing (recovers type from string tag):"
  case parseSomeFoo "int:123" of
    Right sf -> putStrLn $ "   Parsed: " ++ show sf
    Left err -> putStrLn $ "   Error: " ++ err
  case parseSomeFoo "bool:True" of
    Right sf -> putStrLn $ "   Parsed: " ++ show sf
    Left err -> putStrLn $ "   Error: " ++ err
  putStrLn ""

  putStrLn "5. SingKind demote (type-level -> term-level):"
  putStrLn $ "   demote @'TInt = " ++ showDemoted @'TInt
  putStrLn $ "   demote @'TBool = " ++ showDemoted @'TBool
  putStrLn ""

  putStrLn "=== Key Benefit ==="
  putStrLn "All singleton boilerplate generated by one TH splice:"
  putStrLn "  $(singletons [d| data LType = TInt | TBool | TFloat |])"
