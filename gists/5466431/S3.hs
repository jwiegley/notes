loadFromPack dets restart seen sha pack idx len typ mdata = do
    result <- attempts
    case result of
        Left r  -> return r
        Right e -> throwIO (e :: Git.GitException)
  where
    attempts = runEitherT $ do
        htry (getObjectFromPack dets pack idx sha (isNothing mdata))
        htry (translateResult =<< downloadFile dets sha)
        htry (mapM indexPackFile =<< mapM downloadIndex
                  =<< findAllIndices dets sha)

        -- Try the original operation again, with the cache now properly
        -- primed.  However, by passing True to restart we prevent this code
        -- from running the second time.
        left =<< liftIO (restart True)

    htry action = handleData =<< liftIO (try action)

    handleData mresult = case mresult of
        Left e -> right e
        Right (Just (l,t,b)) -> do
            liftIO $ do
                for mdata $ pokeByteString b ?? l
                poke len (toLength l)
                poke typ (toType t)
            left 0
        _ -> right (Git.BackendError
                    "Could not find object in loadFromPack")
