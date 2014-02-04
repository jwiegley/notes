-- | A 'ProjectUpdate' requests that an aspect of the project representation
--   be changed in the isolation-runner.  This list is expected to grow over
--   time.
data ProjectUpdate
    = UpdateFile
      { _updateFilePath         :: TreeFilePath
      , _updateFileModuleStatus :: ModuleStatus
      , _updateFileExcluded     :: Bool
        -- ^ We include the exclusion state here rather than having a separate
        --   request such as ExcludeFile, because we want to avoid a scenario
        --   where the caller tries to exclude the file before registering its
        --   existence with UpdateFile.
      , _updateFileIsTarget     :: Bool
      }
    | RemoveFile
      { _removeFilePath :: TreeFilePath
      }
    | ClearTarget
    deriving (Show, Eq)

makePrisms ''ProjectUpdate
makeClassy ''ProjectUpdate
