zipSinks :: forall a m r r'. (MonadBaseControl IO m, MonadIO m)
         => Sink a m r -> Sink a m r' -> Sink a m (r, r')
zipSinks sink1 sink2 src = do
    x <- liftIO newEmptyMVar
    y <- liftIO newEmptyMVar
    withAsync (sink1 $ sourceMaybeMVar x) $ \a ->
        withAsync (sink2 $ sourceMaybeMVar y) $ \b -> do
            _ <- runEitherT $ runSource src () $ \() val -> do
                liftIO $ putMVar x (Just val)
                liftIO $ putMVar y (Just val)
            liftIO $ putMVar x Nothing
            liftIO $ putMVar y Nothing
            waitBoth a b
