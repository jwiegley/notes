sourceGenerator :: Monad m
                => (forall s. ((Generator s
                                -> Conduit (Generatee s) m Integer)
                               -> Source m Integer))
                -> Source m Integer
sourceGenerator f = f $ \gen -> conduit (go gen)
  where
    go start z yield g = loop start z g
      where
        loop gen r y =
            yield r (reduce y) >>= \r' ->
                let (gen', g) = generate gen
                in loop gen' r' g
