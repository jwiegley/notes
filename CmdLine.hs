cliPushCommit :: MonadCli m
              => CommitOid CliRepo -> Text -> Text -> Maybe FilePath
              -> ReaderT CliRepo m (CommitOid CliRepo)
cliPushCommit cname remoteNameOrURI remoteRefName msshCmd = do
    repo <- getRepository
    merr <- shellyNoDir $ silently $ errExit False $ do
        for_ msshCmd $ \sshCmd ->
            setenv "GIT_SSH" . TL.pack =<< liftIO (canonicalizePath sshCmd)

        eres <- cliRepoDoesExist repo remoteNameOrURI
        case eres of
            Left e -> return $ Just e
            Right () -> do
                git_ repo [ "push", fromStrict remoteNameOrURI
                          , TL.concat [ fromStrict (renderObjOid cname)
                                      , ":", fromStrict remoteRefName
                                      ]
                          ]
                r <- lastExitCode
                if r == 0
                    then return Nothing
                    else Just
                         . (\x -> if "non-fast-forward" `T.isInfixOf` x ||
                                    "Note about fast-forwards" `T.isInfixOf` x
                                 then PushNotFastForward x
                                 else BackendError $
                                          "git push failed:\n" <> x)
                         . toStrict <$> lastStderr
    case merr of
        Nothing  -> do
            mcref <- resolveReference remoteRefName
            case mcref of
                Nothing   -> failure $ BackendError "git push failed"
                Just cref -> return $ Tagged cref
        Just err -> failure err
