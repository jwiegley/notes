iterateM :: (Monad m, MonadBaseControl IO m) => (a -> m a) -> a -> m [a]
iterateM f x = do
    y <- f x
    z <- control $ \run -> unsafeInterleaveIO $ run $ iterateM f y
    return (y:z)
