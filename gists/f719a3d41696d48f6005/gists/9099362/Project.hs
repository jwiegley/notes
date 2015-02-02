checkIdeFileExists :: API.FileName -> RunDB (Maybe API.FileName)
checkIdeFileExists fname =
    fmap (has _Just) $ DB.getBy $ Model.UniqueIdeFile pid fname

helperGetTarget :: HelperIO (Maybe (Either API.FileName Model.RunConfigId))
helperGetTarget = withProject $ \p ->
    case (Model.projectTarget p, Model.projectRunConfig p) of
        (Just fname, _) -> fmap (fmap Left) <$> checkIdeFileExists fname
        (_, Just cid)   -> return $ Just $ Right cid
        _               -> return Nothing

helperSetTarget :: Maybe (Either API.FileName Model.RunConfigId) -> HelperIO ()
helperSetTarget eres = do
    pid <- getProjectId
    fn <- fileName pid eres
    hrunDB $ DB.update pid [ Model.ProjectTarget    DB.=. fn
                           , Model.ProjectRunConfig DB.=. runConfigId eres
                           ]
  where
    fileName pid (Just (Left fname)) = checkIdeFileExists fname
    fileName _ _ = return Nothing

    runConfigId (Just (Right cid)) = Just cid
    runConfigId _ = Nothing

helperGetRunConfig :: Model.RunConfigId -> HelperIO (Maybe Model.RunConfig)
helperGetRunConfig = hrunDB . DB.get
