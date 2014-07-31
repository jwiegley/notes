module Simple

data Source m a where
  Src : r -> (a -> r -> m r) -> m r
