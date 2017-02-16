{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

import Data.Reflection

newtype O a s  = O { runO :: a }

foo :: (Ord k => k -> r) -> r; foo k = k (1 :: int)

-- A dictionary describing an 'Ord' instance.
newtype Ord_ a = Ord_ { compare_ :: a -> a -> Ordering }

-- Utility
isEq :: Ordering -> Bool
isEq EQ = True
isEq _  = False

instance Reifies s (Ord_ a) => Eq (O a s) where
  a == b = isEq (compare_ (reflect a) (runO a) (runO b))

instance (Eq (O a s), Reifies s (Ord_ a)) => Ord (O a s) where
  compare a b = compare_ (reflect a) (runO a) (runO b)
