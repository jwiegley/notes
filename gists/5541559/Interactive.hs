withInteractiveOrProj :: IsolationRunnerState
                      -> Maybe ProjectId
                      -> (SessionManager -> ResourceT IO (ProjectResult a))
                      -> ResourceT IO (ProjectResult a)
withInteractiveOrProj irst Nothing action = do
    register $ atomically (writeTVar (irstInitializing irst) False)

    mmgr <- liftIO $ atomically $ do
        mmgr <- tryReadTMVar (irstInteractive irst)
        when (isNothing mmgr) $ do
            initing <- readTVar (irstInitializing irst)
            check (not initing)
            writeTVar (irstInitializing irst) True
        return mmgr

    action =<< case mmgr of
        Just mgr -> return mgr
        Nothing  -> liftIO $ do
            sess <- initSession $
                    SessionConfig (irstDirectory irst) [] False False
            mgr  <- Mgr.new (irstNextPort irst) sess
            atomically $ putTMVar (irstInteractive irst) mgr
            return mgr
