withInteractiveOrProj :: IsolationRunnerState
                      -> Maybe ProjectId
                      -> (SessionManager -> ResourceT IO (ProjectResult a))
                      -> ResourceT IO (ProjectResult a)
withInteractiveOrProj irst Nothing action = do
    mmgr <- liftIO $ atomically $ tryReadTMVar (irstInteractive irst)
    action =<< case mmgr of
        Just mgr -> return mgr
        Nothing  -> liftIO $ do
            sess <- initSession $
                    SessionConfig (irstDirectory irst) [] False False
            mgr  <- Mgr.new (irstNextPort irst) sess
            atomically $ putTMVar (irstInteractive irst) mgr
            return mgr
