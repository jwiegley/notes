foo queue = atomically $ do
    asyncs <- untilM (readTBQueue queue) (isEmptyTBQueue queue)
    results <- mapM pollSTM asyncs
    -- some of the results will be Nothing, some will be Either e r
    check (length (catMaybes results) == 0)
