    yit "CloneProject" $ do
        uid <- authenticate
        deleteProjects uid

        let repoPath = "CloneProject.git"
        Lg.withLibGitDo $ do
            repo <- liftIO $ createEmptyRepo repoPath True
            liftIO $ void $ runRepository Lg.lgFactory repo $
                populateRepo "refs/heads/master"

        clone <- CloneProject
                 <$> getFayCallToken
                 <*> pure Nothing
                 <*> pure "CloneProject"
                 <*> Cli.cliFilePathToURI repoPath
                 <*> pure "master"

        res <- makeFayCall $ DashboardCommand . clone
        case res of
            Success _ -> runDB $ do
                Just (Entity _ Project {..}) <-
                    selectFirst [ ProjectAuthor ==. uid ] []
                liftIO $ projectTitle `shouldBe` "CloneProject"
            Failure f -> error (show f)
