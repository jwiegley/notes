type Pair a b = (forall r . (a -> b -> r) -> r)

mkPair :: a -> b -> Pair a b
mkPair a b k = k a b
{-# INLINE mkPair #-}

newtype Mealy a b = Mealy { runMealy :: a -> Pair b (Mealy a b) }

combine :: forall a b. Semigroup b => Mealy a b -> Mealy a b -> Mealy a b
combine (Mealy f) (Mealy g) = Mealy (go f g)
 where
  go
    :: (a -> Pair b (Mealy a b))
    -> (a -> Pair b (Mealy a b))
    -> a
    -> Pair b (Mealy a b)
  go f' g' x = f' x go'
   where
    go' a (Mealy b) = g' x go''
     where
      go'' a' (Mealy b') k = let m = a <> a' in m `seq` k m (Mealy (go b b'))
