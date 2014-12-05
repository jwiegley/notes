instance (Monad f, Distributive f, Monad g, Functor g)
         => Monad (Compose f g) where
  return x = Compose $ return (return x)
  Compose m >>= f =
      let x = fmap (fmap (getCompose . f)) m in
      let y = fmap distribute x in
      Compose $ fmap join (join y)
