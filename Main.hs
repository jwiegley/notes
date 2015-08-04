data DFeuer a = DFeuer { getOne :: a, getTwo :: a, getThree :: a }
    deriving Functor

instance Distributive DFeuer where
    distribute x = DFeuer (fmap getOne x) (fmap getTwo x) (fmap getThree x)

instance Representable DFeuer where
    type Rep DFeuer = Int
    tabulate k = DFeuer (k 0) (k 1) (k 2)
    index (DFeuer x y z) = \case
        0 -> x
        1 -> y
        2 -> z
