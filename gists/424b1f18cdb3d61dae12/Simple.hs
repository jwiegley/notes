runGenerator :: Monad m
             => (forall s. ((Generator s
                             -> (Generatee s -> m ())
                             -> m ())
                            -> m ()))
             -> m ()
runGenerator go = go loop
  where
    loop gen k = let (gen', g) = generate gen
                 in k g >> loop gen' k
