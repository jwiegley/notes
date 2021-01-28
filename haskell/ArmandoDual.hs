module ArmandoDual where

class DualFunctor (v :: (* -> *)) a k where
  type Dual v a k
  dual :: DualFunctor w b k => (v a -> w b) -> (Dual w b k -> Dual v a k)

data Yoneda f a = Yoneda (forall r. (a -> r) -> f r)

instance Functor (Yoneda f) where
    fmap g (Yoneda k) = Yoneda $ \h -> k (h . g)

newtype Dualized a b = Dualized (Dual b -> Dual a)

type DualFunctor' a = Yoneda (Dualized a)
