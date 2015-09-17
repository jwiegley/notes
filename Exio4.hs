{-# LANGUAGE FlexibleInstances, GADTs, OverloadedStrings #-}

import GHC.Exts

data Param a where
      Str :: String -> Param String
      Flt :: Float  -> Param Float

instance (a ~ String) => IsString (Param a) where
    fromString = Str

instance (a ~ Float) => Num (Param a) where
    fromInteger = Flt . fromInteger
    Flt x + Flt y = Flt (x+y)
    Flt x - Flt y = Flt (x-y)
    Flt x * Flt y = Flt (x*y)
    abs (Flt x) = Flt (abs x)
    signum (Flt x) = Flt (signum x)
-- and other instances following the same patterns..

magic :: Param a -> Int
magic (Str x) = length x
magic (Flt x) = floor (toRational x)
