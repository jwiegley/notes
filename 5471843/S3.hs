type HardlyT m a = EitherT a m ()

found :: Monad m => a -> HardlyT m a
found = left

continue :: Monad m => HardlyT m a
continue = right ()

accessObject :: (OdbS3Details -> Text -> CacheInfo -> a
                 -> HardlyT IO b)
             -> a
             -> b
             -> OdbS3Details
             -> Text
             -> IO b
accessObject f arg dflt dets sha =
    eitherT return (const (return dflt)) $ do
        mstatus <- lift $ cacheObjectInfo dets sha
        maybe continue go mstatus

        mstatus <- lift $ callbackObjectInfo dets sha
        for mstatus $ \status -> do
            lift $ cacheRecordInfo dets sha status
            go status

        mstatus <- lift $ remoteObjectInfo dets sha
        for mstatus $ \status -> do
            lift $ cacheRecordInfo dets sha status
            lift $ callbackRecordInfo dets sha status
            go status

        lift $ remoteCatalogContents dets

        mstatus <- lift $ cacheObjectInfo dets sha
        for mstatus $ \status -> do
            lift $ callbackRecordInfo dets sha status
            go status

        left dflt
  where
    go = f dets sha ?? arg

objectExists :: OdbS3Details -> Text -> IO Bool
objectExists = accessObject (\_ _ status _ ->
                              left (status /= DoesNotExist))
                   () False
