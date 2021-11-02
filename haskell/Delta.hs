{-# LANGUAGE TypeFamilies #-}

module Delta where

class Delta a where
  type Change a

data Delta a => Changed a = Unchanged | Changed (Change a)

assertChanges :: Delta a => a -> a -> Changed a -> IO ()
assertChanges = undefined

data IntChange = IntChange Int Int

data Product = Product
  { foo :: Int,
    bar :: Int,
    baz :: Int
  }

instance Delta Product where
  type Change Product = [ProductChange]

-- GENERATED
data ProductChange
  = ProductFoo IntChange
  | ProductBar IntChange
  | ProductBaz IntChange

data Sum
  = Foo Int Int Int
  | Bar Int Int Int
  | Baz Int Int Int

instance Delta Sum where
  type Change Sum = SumChange

-- GENERATED
data SumChange
  = SumFoo [SumFooChange]
  | SumBar [SumBarChange]
  | SumBaz [SumBazChange]

-- GENERATED
data SumFooChange
  = SumFoo0 IntChange
  | SumFoo1 IntChange
  | SumFoo2 IntChange

-- GENERATED
data SumBarChange
  = SumBar0 IntChange
  | SumBar1 IntChange
  | SumBar2 IntChange

-- GENERATED
data SumBazChange
  = SumBaz0 IntChange
  | SumBaz1 IntChange
  | SumBaz2 IntChange

main :: IO ()
main = do
  assertChanges (Product 1 2 3) (Product 1 10 3) $
    Changed [ProductBar (IntChange 2 10)]

  assertChanges (Bar 1 2 3) (Bar 1 10 3) $
    Changed (SumBar [SumBar1 (IntChange 2 10)])
