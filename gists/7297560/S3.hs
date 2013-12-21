embedIO :: (MonadBaseControl IO m, MonadIO m) => (a -> m b) -> m (a -> base b)
embedIO f = liftBaseWith $ \run -> do
    result <- newIORef undefined
    -- Return an IO action that closes over the current monad transformer, but
    -- throws away any residual effects within that transformer.
    return $ \a -> do
        _ <- run $ do
            res <- f a
            liftIO $ writeIORef result res
        readIORef result
