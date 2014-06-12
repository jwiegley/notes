sourceGenerator :: Monad m
                => (forall s. ((Generator s -> Source m (Generatee s)) -> m a))
                -> m a
sourceGenerator f = f $ \gen -> source (go gen)
  where
    go start z yield = loop start z
      where
        loop gen r =
            let (gen', g) = generate gen
            in yield r g >>= loop gen'
