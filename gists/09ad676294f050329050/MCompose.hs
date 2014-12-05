instance (Monad f, Applicative f, Monad g, Traversable g)
         => Monad (Compose f g) where
  return x = Compose $ return (return x)
  Compose m >>= f = Compose $ do
      let x = liftM (fmap (getCompose . f)) m
      liftM join (join (liftM sequenceA x))
