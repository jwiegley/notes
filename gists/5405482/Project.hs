getImportedPackages' :: IsolationRunnerState
                     -> ProjectId
                     -> ResourceT IO (ProjectResult [PackageId])
getImportedPackages' irst pname = do
    liftIO $ log "Getting type information for range"
    applyToProject irst (Just pname) LoadingManager $ \mgr mmprj ->
        maybe (return NeedProjectInfo) (getPackageImports mgr) mmprj
  where
    getPackageImports mgr _ = do
        let session = mgrSession mgr
        mods <- liftIO $ getLoadedModules session
        impf <- liftIO $ getImports session
        return
            . ProjectResult
            . nub
            . sort
            . map (modulePackage . importModule)
            . concat
            . catMaybes
            . map impf
            $ mods
