newtype ComposeT (f :: (* -> *) -> * -> *) (g :: (* -> *) -> * -> *) m a
    = ComposeT { getComposeT :: f (g m) a }
    deriving (Functor, Applicative, Monad, MonadIO)

instance (MFunctor f, MonadTrans f, MonadTrans g)
         => MonadTrans (ComposeT f g) where
    lift = ComposeT . hoist lift . lift

instance (MonadIO (f (g m)), Applicative (f (g m)))
         => MonadBase IO (ComposeT f g m) where
    liftBase = liftIO

instance (Applicative (f (g m)), MonadBaseControl IO (f (g m)),
          MonadIO (f (g m)))
         => MonadBaseControl IO (ComposeT f g m) where
    newtype StM (ComposeT f g m) a = StMComposeT (StM (f (g m)) a)
    liftBaseWith f =
        ComposeT $ liftBaseWith $ \runInBase -> f $ \k ->
            liftM StMComposeT $ runInBase $ getComposeT k
    restoreM (StMComposeT m) = ComposeT . restoreM $ m
