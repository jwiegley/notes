instance (Representable g, Monad g, Monad f) => Monad (Compose g f) where
    return = Compose . return . return
    Compose x >>= f = Compose $ join $ tabulate $ \k ->
        fmap (join . liftM ((`R.index` k) . getCompose . f)) x
