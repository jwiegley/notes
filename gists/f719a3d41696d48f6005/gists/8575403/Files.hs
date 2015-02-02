data ProjectUpdate
    = SetTarget
    | UpdateFile
    | RemoveFile
    deriving Show

updateProject :: ProjectUpdate
              -> RWS (IsolationRunnerState, IsolationRunnerProject)
                  CompileJob ProjectFileInfo ()
