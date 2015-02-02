runProcess :: Text -> [Text] -> Bool -> RunnerIO Text
runProcess cmd args ignoreOutput = do
    dir <- projectWorkingDirectory
    tempDir <- liftIO getTemporaryDirectory
    withTempFile tempDir "stdout" $ \outPath outh ->
        withTempFile tempDir "stdrr" $ \errPath errh -> do
            h <- Process.runProcess
                (unpack cmd)
                (map unpack args)
                (Just dir)
                Nothing
                Nothing
                (Just outh)
                (Just errh)
            status <- waitForProcess h
            hClose outh
            hClose errh
            case status of
                ExitSuccess
                    | ignoreOutput -> return ""
                    | otherwise    -> T.readFile outPath
                ExitFailure r -> do
                    err <- T.readFile errPath
                    failure $ "Command " ++ tshow cmd ++ " "
                           ++ tshow (concat (intersperse " " args)) ++ " "
                           ++ " failed with exit code " ++ tshow r
                           ++ ": " ++ err
