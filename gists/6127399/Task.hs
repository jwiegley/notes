waitOnTaskStatus :: TaskStatus s
                 => TaskId s -> Bool -> SessionManager s -> STM (Maybe s)
waitOnTaskStatus tid anyNonReady mgr = do
    mstatus <- getTaskStatus tid mgr
    forM_ mstatus $ \status -> case taskState status of
        TaskReady    -> retry
        TaskStarting -> retry
        TaskRunning  -> unless anyNonReady retry
        TaskDone     -> modifyTVar (mgrTasks mgr) $ delete tid
        TaskFailed   -> modifyTVar (mgrTasks mgr) $ delete tid
    return mstatus
