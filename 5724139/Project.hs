checkoutRef :: Entity Project
            -> Text -- ^ reference name
            -> Handler ()
checkoutRef projent@(Entity pid Project {..}) rname = runDB $ do
    mref <- do
        Entity repoid _ <- getProjectRepo pid
        getBy $ UniqueGitRef repoid rname
    case mref of
        Nothing  -> fail $ "Reference " ++ show rname ++ " not found"
        Just ref -> go ref
  where
    go ref = do
        let sha = gitRefCommit (entityVal ref)
        resetProject projent sha

        -- Update the user's project branch and base commit
        update pid [ ProjectBaseCommit =. Just sha
                   , ProjectBranch     =. rname ]

        -- For completeness sake (and it helps with debugging), update the
        -- ref in the Git repository itself as well.  For S3 this is
        -- meaningless, but when running local tests it's meaningful.
        ogr  <- getOpenGitRepo
        repo <- liftIO $ ogr $ ProjectRepo pid
        liftIO $ Lg.runLgRepository repo $ do
            coid <- parseOid (unCommitSHA sha)
            updateRef_ rname (RefObj (ByOid (Tagged coid)))
