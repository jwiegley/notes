cancelAll :: Pool -> IO ()
cancelAll p = (mapM_ cancel =<<) $ atomically $ do
    writeTVar (p^.tasks) Gr.empty
    xs <- IntMap.elems <$> readTVar (p^.procs)
    writeTVar (p^.procs) mempty
    return xs
