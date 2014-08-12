instance MonadBaseControl IO Sh where
    newtype StM Sh a = StMSh (StM (ReaderT (IORef State) IO) a)
    liftBaseWith f =
        Sh $ liftBaseWith $ \runInBase -> f $ \k ->
            liftM StMSh $ runInBase $ unSh k
    restoreM (StMSh m) = Sh . restoreM $ m
