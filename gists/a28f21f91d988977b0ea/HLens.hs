h :: (Distributive m1, Monad m1, Functor m2, Monad m2)
  => (b -> m1 (m2 c)) -> (a -> m1 (m2 b)) -> a -> m1 (m2 c)
h f g = liftM join . join . liftM (distribute . liftM f) . g
