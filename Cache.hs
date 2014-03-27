sinkFileThroughTemp :: (MonadBaseControl IO m, MonadResource m, IOData a)
                    => FilePath -> Consumer a m ()
sinkFileThroughTemp path = do
    tmpDir <- liftIO getTemporaryDirectory
    (name, h) <- liftIO $ openTempFile tmpDir "sink."
    catchC (sinkHandle h) $ \(e :: SomeException) -> liftIO $ do
        hClose h
        removeFile name
        throwIO e
    liftIO $ do
        hClose h
        renameFile name (fpToString path)
