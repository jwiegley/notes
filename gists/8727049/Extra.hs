iterateM :: Monad m => (a -> m a) -> a -> m [a]
iterateM f x = do
    x' <- f x
    (x':) `liftM` iterateM f x'
