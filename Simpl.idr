module Simple

data Source : (m : Type -> Type) -> (a : Type) -> Type where
  Src : r -> (a -> r -> m r) -> m r -> Source m a

instance Functor (Source m) where
    fmap f (Src await) = Src $ \z yield => await z (yield . f)
