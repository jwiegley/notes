module CurryM where

uncurryM :: Monad m => (a -> m (b -> m c)) -> ((a, b) -> m c)
uncurryM f (a, b) = do
  f' <- f a
  f' b

curryM :: Monad m => ((a, b) -> m c) -> (a -> m (b -> m c))
curryM f a = do
  f (a, !)
