{-# LANGUAGE UndecidableInstances #-}

import Data.Reflection

newtype O a s  = O { runO :: a }

-- A dictionary describing an 'Ord' instance.
newtype Ord_ a = Ord_ { compare_ :: a -> a -> Ordering }

instance Reifies s (Ord_ a) => Ord (O a s) where
    compare x y = compare_ (reflect x) x y
