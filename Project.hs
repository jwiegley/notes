projectWorkingDiff :: Entity Project -> Handler (Either Text ByteString)
projectWorkingDiff (Entity projid Project {..}) = $runDB $ do
    case projectBaseCommit of
        Nothing  -> return $ Left "Project has no known base commit"
        Just sha -> do
            let mf (Entity _ m) = do
                    yield $ Left $ unDataFileName $ moduleGitPath m
                    yield $ Right $ encodeUtf8 $ moduleContents m
                df (Entity _ m) = case dataFileContents m of
                    Nothing -> return ()
                    Just content -> do
                        yield $ Left $ unDataFileName $ dataFileName m
                        yield $ Right content
                modules = selectSource [ModuleProject ==. projid] []
                              $= awaitForever mf
                dataFiles = selectSource [DataFileProject ==. projid] []
                                $= awaitForever df
            repo <- openProjectRepo projid
            fmap Right $ Lg.runLgRepository repo $ do
                commitoid <- parseObjOid (unCommitSHA sha)
                commit <- lookupCommit commitoid
                tree <- lookupTree (commitTree commit)
                bs <- diffContentsWithTree (modules >> dataFiles) tree
                    $$ CB.sinkLbs
                return $ toStrict bs
