data Sum f g a = InL (f a) | InR (g a) deriving Show

instance (Functor f, Functor g) => Functor (Sum f g) where
    fmap f (InL x) = InL (fmap f x)
    fmap f (InR y) = InR (fmap f y)

class Natural f g where
    eta :: f a -> g a

instance (Applicative f, Applicative g, Natural g f)
         => Applicative (Sum f g) where
    pure x = InR (pure x)
    InL f <*> InL x = InL (f <*> x)
    InR g <*> InR y = InR (g <*> y)
    InL f <*> InR x = InL (f <*> eta x)
    InR g <*> InL x = InL (eta g <*> x)

instance Natural m (Const String) where
    eta _ = undefined
