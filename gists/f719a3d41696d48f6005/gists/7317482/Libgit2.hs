newtype TCompose (f :: (* -> *) -> * -> *) (g :: (* -> *) -> * -> *) m a
    = TCompose { getTCompose :: f (g m) a }
