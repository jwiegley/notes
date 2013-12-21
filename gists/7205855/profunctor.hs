class (Functor f, Profunctor p) => PApplicative f p where
    pure :: a -> p (f ()) (f a)
    (<*>) :: f (p a b) -> p (f a) (f b)

instance (Functor f, Copointed f) => PApplicative f (->) where
    pure x = fmap (\() -> x)
    (<*>) = copoint . fmap distrib
