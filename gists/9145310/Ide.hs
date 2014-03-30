module FP.IsolationRunner.Jobs.Ide where

import ClassyPrelude.Conduit hiding (log)
import Control.Exception.Lifted
import Control.Concurrent.Lifted (fork)
import Control.Concurrent.STM
import Data.Bifunctor
import FP.API as API
import FP.IsolationRunner.Ide.Command
import FP.IsolationRunner.Project.Create
import FP.IsolationRunner.Types
import FP.IsolationRunner.Utils

runIdeJob :: API.JobId -> IdeJob -> RunnerIO ()
runIdeJob _jid (IdeJob cmd resultVar) = mask $ \unmask -> do
    result <- try $ unmask (runIdeCommand cmd)
    atomicallyM $ putTMVar resultVar result

runIdeJob jid (IdeAsyncJob cmd) = mask $ \unmask -> do
    result <- try $ unmask (runIdeCommand cmd)
    projectMessage (Just jid) $
        API.IdeCommandOutput (bimap tshow id $ result)

runIdeJob _jid IdeCloseProject = do
    pid <- getProjectId
    void $ fork $ void $ liftRunnerBase $ closeProject' pid
