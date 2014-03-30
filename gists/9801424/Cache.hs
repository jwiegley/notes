sinkFileThroughTemp :: (MonadBaseControl IO m, MonadResource m, IOData a)
                    => FilePath -> Consumer a m ()
sinkFileThroughTemp path = do
    tmpDir <- liftIO getTemporaryDirectory
    (key, (name, h)) <- allocate (openTempFile tmpDir "sink.") $
        \(name, h) -> hClose h >> void (tryAny (removeFile name))
    sinkHandle h
    liftIO $ do
        hClose h
        renameFile name (fpToString path) `catchAny` \_ ->
            runResourceT (sourceFile (fpFromString name) $$
                 (sinkFile path :: Consumer ByteString (ResourceT IO) ()))
    void $ unprotect key
