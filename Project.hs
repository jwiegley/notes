projectMergeDone :: Text -- ^ URL
                 -> MaybeText -- ^ Commit message
                 -> Entity Project
                 -> Handler (Either Text GitResolvedResult)
projectMergeDone "" _ _ = return $ Left "No URL provided"
projectMergeDone _ mmsg projent@(Entity pid Project {..}) =
    case stripPrefix "merge/" projectBranch of
        Nothing         -> return $ Left "There is no merge to complete."
        Just prevBranch -> do
            mref <- runDB $ do
                Entity repoid _ <- getProjectRepo pid
                getBy $ UniqueGitRef repoid $ mergeRef prevBranch
            case mref of
                Nothing  -> fail "Merge reference is missing"
                Just ref -> go prevBranch (gitRefCommit (entityVal ref))
  where
    go prevBranch sha = do
        (modules,dataFiles) <- runDB $ do
            modules <- selectList [ModuleProject ==. pid] [Asc ModuleName]
            dataFiles <- selectList [DataFileProject ==. pid] [Asc DataFileName]
            return (map entityVal modules, map entityVal dataFiles)
        let conflicts = catMaybes
                      $ map getDataFileMergeConflict dataFiles
                     ++ map getModuleMergeConflict modules
        if not (null conflicts)
            then return $ Right $ GRRStillUnresolved conflicts
            else do
                ogr <- runDB getOpenGitRepo
                repo <- liftIO $ ogr $ ProjectRepo pid

                -- Load in all the modules and data files, and amend the merge
                -- commit to reflect the now-resolved state.  We don't know
                -- which files may have been edited, so we will add them all
                -- to Git and let its hashing algorithm discover the real
                -- changes.
                ecommit <- try $ Lg.runLgRepository repo $
                    parseOid (unCommitSHA sha)
                        >>= lookupCommit . Tagged
                        >>= amendCommit
                recordCommit prevBranch ecommit

    amendCommit commit = do
        tr <- newTree
        populateTree projent tr

        commitOid <$> createCommit
            (commitParents commit)
            (Known tr)
            (commitAuthor commit)
            (commitCommitter commit)
            (case mmsg of
                  NoText -> commitLog commit
                  JustText msg -> msg)
            Nothing
