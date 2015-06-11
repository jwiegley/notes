athan :: (MonadTrans t, Monad (t m), Monad m) => (a -> m b) -> t m a -> t m b
athan f m = m >>= lift . f
