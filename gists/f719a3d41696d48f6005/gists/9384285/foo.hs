downloadRepository :: Prelude.FilePath -> RunnerIO ()
downloadRepository dir = timedLog "Downloading repository" dir $ do
    pid <- getProjectId
    let prefix = if pid == interactive
                 then "tutorial"
                 else "project" </> unpack (toPathPiece pid)
    objects <- helperS3GetBucket (pack prefix)
    forM_ objects $ \(unpack -> object) -> do
        src <- helperS3GetObject (pack object)
        let dest = localPath object
        liftIO $ createDirectoryIfMissing True (takeDirectory dest)
        runResourceT $ hoist lift src
            -- Our S3 store keep 16 bytes of metadata at the beginning of
            -- every file stored there.
            $$ dropCE (sizeOf (0 :: Int64) * 2)
            >> sinkFile (fpFromString dest)
    prj <- getProject
    repo <- openRepository Cli.cliFactory RepositoryOptions
        { repoPath       = dir
        , repoIsBare     = False
        , repoAutoCreate = True
        }
    -- By putting this repository in the project, we signal that the local Git
    -- repository is ready for use.
    atomicallyM $ do
        writeTVar (projRepoObjects prj) (sort objects)
        putTMVar (projCliRepository prj) repo
  where
    localPath path
        | ".idx" `isSuffixOf` path || ".pack" `isSuffixOf` path =
            dir </> "objects" </> "pack" </> path
        | otherwise =
            dir </> "objects" </> take 2 path </> drop 2 path

pushLocalRepository :: RunnerIO ()
pushLocalRepository = timedLog "Uploading repository" () $ do
    log "Pushing local Git changes to S3..."
    -- We collect garbage before uploading to make the upload more efficient
    git_ [ "gc" ]
    git_ [ "prune" ]
    -- Get the list of objects, and find out what is new from what we knew was
    -- in S3.  call helperS3PutObject for each of those.
    projDir <- getProjectDirectory
    let dir = projDir </> "repo" </> ".git" </> "objects"
    prj <- getProject
    objects <- atomicallyM $ readTVar (projRepoObjects prj)
    xs <- Files.traverse False (fpFromString dir)
        $= concatMapC (\p -> (,p) <$> fpToRemote dir p)
        $$ sinkList
    let objects' = sort $ map fst xs
    pid <- getProjectId
    let prefix = if pid == interactive
                 then "tutorial"
                 else "project" </> unpack (toPathPiece pid)
    forM_ (objects' \\ objects) $ \object ->
        case lookup object xs of
            Nothing -> log $ "Ignoring file: " ++ object
            Just path -> runResourceT $ do
                is <- getInternalState
                lift $ helperS3PutObject (pack (prefix </> unpack object)) $ do
                    -- Our S3 store keep 16 bytes of metadata at the beginning
                    -- of every file stored there.
                    yield $ replicate (sizeOf (0 :: Int64) * 2) 0
                    hoist (flip runInternalState is) $ sourceFile path
    atomicallyM $ writeTVar (projRepoObjects prj) objects'
  where
    fpToRemote dir = remotePath . pack . makeRelative dir . fpToString

    remotePath path
        | "pack/" `isPrefixOf` path = Just $ drop 5 path
        | "/" `isPrefixOf` drop 2 path = Just $ take 2 path ++ drop 3 path
        | otherwise = Nothing
