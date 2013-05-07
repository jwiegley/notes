-- | Halt a currently running process, or do nothing if no process is running.
stop :: PID -> SessionManager -> IO ()
stop pid mgr = do
    log $ "Stopping process " ++ show pid
    -- It's always possible that between this call to 'getProcStatus', and the
    -- call to 'killProcess', that the process might have exited naturally.
    -- In that case, it's important that killing a dead process be idempotent,
    -- with the only effective result being that its status is set immediately
    -- to 'PSInterrupted'.
    mps <- atomically $ do
          mps <- getProcStatus pid mgr
          case mps of
              Just (PSReady {..}) -> do
                  -- We must handle cancelling a process within the atomic
                  -- block, otherwise it might start running before we have a
                  -- chance to cancel it.
                  putProcStatus psProcessId PSCanceled mgr
                  return Nothing
              _ -> return mps
    case mps of
        Just (PSRunning r tid) -> do
            log "Process was running, killing it"
            -- Make sure the helper thread dies too, although it should exit
            -- naturally from the killProcess
            finally (killProcess r) (killThread tid)
        _ -> return ()
