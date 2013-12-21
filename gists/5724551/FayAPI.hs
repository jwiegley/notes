    yit "DownloadBinary" $ do
        uid <- authenticate
        deleteProjects uid

        let repoPath = "git-repos/DownloadBinary.git"
        (pid, _c) <- cloneNewProject uid repoPath
        let fpid = FayProjectId (keyText pid)

        gen <- ideCommand (AddModule (FayModuleName "Main") fpid) return
        ideCommand_ (GetCompileErrors gen fpid)

        token <- ideCommand (GetModuleToken
                             (FayModuleName "Main") fpid) return
        let source = "module Main where\n\
                     \\n\
                     \main = putStrLn \"Hello, world!\"\n"
        ideCommand_ (SaveModule (FayModuleName "Main") source token fpid)
        content <- ideCommand (GetModule (FayModuleName "Main") fpid) return
        liftIO $ mcText content `shouldBe` source

        ideCommand_ (CommitToGit "Added Main.hs file.\n" fpid)
        gitUri <- Cli.cliFilePathToURI repoPath
        ideCommand_ (GitPush gitUri fpid)

        ideCommand_ (SetTargetType (FayModuleName "Main")
                     (Just TargetConsole) fpid)
        path <- ideCommand (DownloadBinary (FayModuleName "Main") fpid) return
        liftIO $ putStrLn $ "step 7: " ++ show path
