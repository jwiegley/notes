This is the FP Complete fpco-api buffer. To kill the server, just kill this buffer.

-- Command: 
-- 
-- fpco-api start --agent Emacs

Vulcan:~ $ bash: fpco-api: command not found
Vulcan:~ [127] $ ~/fpco/fpco-api/dist/build/fpco-api/fpco-api start --agent Emacs
[Info] Server started on port 1990, remote URL is: https://learning-site-staging.fpcomplete.com @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:71:5)

[Info] Connection accepted from: localhost:61292 ({handle: <socket: 13>}) @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:81:5)

[Debug] <- MsgCheckModule (FayProjectId {unFayProjectId = "349"}) "/Users/johnw/src/fuzzcheck-intro/" "src/Main.hs" "/var/folders/88/wc6xbg9n1s97wzn8rrw5n_h40000gn/T/flycheck26732Dib/Main.hs" @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:98:13)

[Debug] => IdeCommand (GetFileToken (FayFileName {unFayFileName = "src/Main.hs"}) (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= TutorialConcurrentToken' {unTutorialConcurrentToken = 53} @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (SaveFile (FayFileName {unFayFileName = "src/Main.hs"}) "-- | Main entry point to the application.\nmodule Main where\n\nimport … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= SaveFileOutput (TutorialConcurrentToken' {unTutorialConcurrentToken = 54}) (CompileChanged {ccCompileId = Nothing, ccFiles = [FileChanged {… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] Updating file token: /Users/johnw/src/fuzzcheck-intro/src/Main.hs: TutorialConcurrentToken' {unTutorialConcurrentToken = 54} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:468:5)

[Debug] -> ReplyCompileInfos [] @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:340:5)

[Debug] Connection closed to {handle: <socket: 13>} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:346:5)

[Info] Connection accepted from: localhost:61295 ({handle: <socket: 13>}) @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:81:5)

[Debug] <- MsgAutoComplete (FayProjectId {unFayProjectId = "349"}) "src/Main.hs" "putStrLnxp" @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:98:13)

[Debug] => IdeCommand (GetAutocompletions (AutoCompleteInput {aciModuleName = FayFileName {unFayFileName = "src/Main.hs"}, aciPrefix = "putStrLnxp"}) … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Info] Connection accepted from: localhost:61297 ({handle: <socket: 16>}) @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:81:5)

[Debug] <- MsgCheckModule (FayProjectId {unFayProjectId = "349"}) "/Users/johnw/src/fuzzcheck-intro/" "src/Main.hs" "/var/folders/88/wc6xbg9n1s97wzn8rrw5n_h40000gn/T/flycheck26732Qsh/Main.hs" @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:98:13)

[Debug] => IdeCommand (SaveFile (FayFileName {unFayFileName = "src/Main.hs"}) "-- | Main entry point to the application.\nmodule Main where\n\nimport … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= () @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetInitialProjectInfo (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= SaveFileOutput (TutorialConcurrentToken' {unTutorialConcurrentToken = 55}) (CompileChanged {ccCompileId = Just (CompileId {unCompileId = 2}… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] Updating file token: /Users/johnw/src/fuzzcheck-intro/src/Main.hs: TutorialConcurrentToken' {unTutorialConcurrentToken = 55} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:468:5)

[Debug] <= InitialProjectInfo {ipiTitle = "fuzzcheck-intro", ipiDesc = "", ipiGitUrl = Nothing, ipiMergeConflicts = Nothing, ipiInvalidSettings = Fals… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] Polling on project FayProjectId {unFayProjectId = "349"} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:386:5)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpening "Creating empt… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "8268693189534726991")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 1) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpening "Con… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "9211955005720116432")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 2) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpening "Bui… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "-6677225254619917427")) (FayProjectId {unFayProjectId = … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 3) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpening "Cop… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "-2389237064980682784")) (FayProjectId {unFayProjectId = … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 4) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpening "Reg… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "-4918880883510552668")) (FayProjectId {unFayProjectId = … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 5) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpening "Ini… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "4857868870376387551")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 6) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpening "All… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "-8639561121312623299")) (FayProjectId {unFayProjectId = … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 7) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCo… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "3659502603655613546")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 8) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCo… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "-9191993159472691990")) (FayProjectId {unFayProjectId = … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 9) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCo… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] -> ReplyCompileInfos [SourceInfo {infoKind = KindError, infoSpan = ProperSpan (SourceSpan {spanFilePath = FayFileName {unFayFileName = "src/Ma… @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:340:5)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "419282685566463093")) (FayProjectId {unFayProjectId = "3… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] Connection closed to {handle: <socket: 16>} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:346:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 11) [(Just 1,AutoCompleteResults (Just (AutoCompleteInput {aciModuleName = FayFileName {unFayFile… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] -> ReplyCompletions [] @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:340:5)

[Debug] => IdeCommand (GetProjectMessages (PMRImmediateStatusWithMessages (PMFilterOnOrBefore 11)) (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] Connection closed to {handle: <socket: 13>} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:346:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 12) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapC… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "419282685566463093")) (FayProjectId {unFayProjectId = "3… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Info] Connection accepted from: localhost:61314 ({handle: <socket: 13>}) @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:81:5)

[Debug] <- MsgCheckModule (FayProjectId {unFayProjectId = "349"}) "/Users/johnw/src/fuzzcheck-intro/" "src/Main.hs" "/var/folders/88/wc6xbg9n1s97wzn8rrw5n_h40000gn/T/flycheck26732d2n/Main.hs" @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:98:13)

[Debug] => IdeCommand (SaveFile (FayFileName {unFayFileName = "src/Main.hs"}) "-- | Main entry point to the application.\nmodule Main where\n\nimport … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 13) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapC… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "8840904276557502747")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= SaveFileOutput (TutorialConcurrentToken' {unTutorialConcurrentToken = 56}) (CompileChanged {ccCompileId = Just (CompileId {unCompileId = 5}… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] Updating file token: /Users/johnw/src/fuzzcheck-intro/src/Main.hs: TutorialConcurrentToken' {unTutorialConcurrentToken = 56} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:468:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 14) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapC… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] -> ReplyCompileInfos [] @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:340:5)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "-431123282954994530")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] Connection closed to {handle: <socket: 13>} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:346:5)

[Info] Connection accepted from: localhost:61318 ({handle: <socket: 14>}) @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:81:5)

[Debug] <- MsgSaveModule (FayProjectId {unFayProjectId = "349"}) "/Users/johnw/src/fuzzcheck-intro/" "src/Main.hs" @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:98:13)

[Debug] => IdeCommand (SaveFile (FayFileName {unFayFileName = "src/Main.hs"}) "-- | Main entry point to the application.\nmodule Main where\n\nimport … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Info] Connection accepted from: localhost:61320 ({handle: <socket: 17>}) @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:81:5)

[Debug] <- MsgCheckModule (FayProjectId {unFayProjectId = "349"}) "/Users/johnw/src/fuzzcheck-intro/" "src/Main.hs" "/var/folders/88/wc6xbg9n1s97wzn8rrw5n_h40000gn/T/flycheck26732qAu/Main.hs" @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:98:13)

[Debug] => IdeCommand (SaveFile (FayFileName {unFayFileName = "src/Main.hs"}) "-- | Main entry point to the application.\nmodule Main where\n\nimport … @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] Error from request: SaveFile (FayFileName {unFayFileName = "src/Main.hs"}) "-- | Main entry point to the application.\nmodule Main where\n\nimport Control.Monad.Loops\n\n{-\n\nThis is an introduction to the FuzzCheck library, which aims to make it easy to\nenrich your monad-based tests using some of the functionality of QuickCheck.\n\n-}\n\nimport Test.FuzzCheck\n\n-- | The main entry point.\nmain :: IO ()\nmain = do\n    putStrLn \"Welcome to FP Haskell Center!\"\n    putStrLn \"Have a good day!\"\n" (TutorialConcurrentToken' {unTutorialConcurrentToken = 56}) (FayProjectId {unFayProjectId = "349"}) Returns
<= Out of date content @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:86:31)

[Debug] -> ReplyCompileInfos [] @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:340:5)

[Debug] Connection closed to {handle: <socket: 17>} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:346:5)

[Debug] <= SaveFileOutput (TutorialConcurrentToken' {unTutorialConcurrentToken = 57}) (CompileChanged {ccCompileId = Just (CompileId {unCompileId = 9}… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] Updating file token: /Users/johnw/src/fuzzcheck-intro/src/Main.hs: TutorialConcurrentToken' {unTutorialConcurrentToken = 57} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:468:5)

[Debug] -> ReplySaveStatus False @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:340:5)

[Debug] Connection closed to {handle: <socket: 14>} @(fpco-api-1.0.0:FP.Server src/library/FP/Server.hs:346:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 15) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapC… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6905783958150589943")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput (PMFilterOnOrBefore 16) [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapC… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [] @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages PMRImmediateStatusNoMessages (FayProjectId {unFayProjectId = "349"}) Returns) @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

[Debug] <= ProjectMessagesOutput PMFilterNone [(Nothing,StatusSnapshot (ProjectStatusSnapshot {snapOpeningStatus = RunnerProjectOpen, snapCompileStatu… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:88:31)

[Debug] => IdeCommand (GetProjectMessages (PMRNextStatusWithMessages PMFilterAll (StatusHash "6700518671448174682")) (FayProjectId {unFayProjectId = "… @(fpco-api-1.0.0:FP.API.Run src/library/FP/API/Run.hs:74:5)

