    go gitDir coid = do
        coid' <- copyCommitOid coid
        -- cref  <- pushCommit (CommitObjectId coid') Nothing rname
        repo <- getRepository Lg.lgFactory
        liftIO $ withForeignPtr (Lg.repoObj repo) $ \repoPtr ->
            withCString (T.unpack (toTextIgnore gitDir)) $ \gitDirStr ->
                alloca $ runResourceT . downloadPack repoPtr gitDirStr
        -- updateRef_ rname (RefObj cref)
        return ()

    downloadPack repoPtr gitDirStr remotePtrPtr = do
        r <- liftIO $ c'git_remote_create_inmemory
                 remotePtrPtr repoPtr nullPtr gitDirStr
        checkResult r "c'git_remote_new failed"
        remotePtr <- liftIO $ peek remotePtrPtr
        register (c'git_remote_free remotePtr)

        r <- liftIO $ c'git_remote_connect remotePtr c'GIT_DIRECTION_FETCH
        checkResult r "c'git_remote_connect failed"
        register (c'git_remote_disconnect remotePtr)

        r <- liftIO $ c'git_remote_download remotePtr nullFunPtr nullPtr
        checkResult r "c'git_remote_download failed"
