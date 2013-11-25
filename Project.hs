projectWorkingDiff :: Entity Project -> Handler (Either Text ByteString)
projectWorkingDiff (Entity projid Project {..}) =
    case projectBaseCommit of
        Nothing  -> return $ Left "Project has no known base commit"
        Just sha -> go sha
  where
    go sha = do
        repo <- openProjectRepo projid
        Lg.runLgRepository repo $ $runDB $ do
            commitoid <- parseObjOid (unCommitSHA sha)
            commit <- lookupCommit commitoid
            tree <- lookupTree (commitTree commit)
            bs <- diffContentsWithTree (modules >> dataFiles) tree $$ CB.sinkLbs
            return $ Right $ toStrict bs

    modules = selectSource [ModuleProject ==. projid] []
        $= awaitForever mf
      where
        mf (Entity _ m) = do
            yield $ Left $ unDataFileName $ moduleGitPath m
            yield $ Right $ encodeUtf8 $ moduleContents m

    dataFiles = selectSource [DataFileProject ==. projid] []
        $= awaitForever df
      where
        df (Entity _ m) = case dataFileContents m of
            Nothing -> return ()
            Just content -> do
                yield $ Left $ unDataFileName $ dataFileName m
                yield $ Right content
