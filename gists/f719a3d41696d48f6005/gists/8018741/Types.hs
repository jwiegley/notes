data IsolationRunnerInteractive = IsolationRunnerInteractive
    { interMessages :: TChan ByteString         -- process output
    , interStatus   :: TVar RunnerProcessStatus -- process status
    }
