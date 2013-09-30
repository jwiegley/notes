    attempts = runEitherT $ do
        htry (getObjectFromPack dets pack idx sha (isNothing mdata))
        htry (translateResult =<< downloadFile dets sha)
        htry (mapM indexPackFile =<< mapM downloadIndex
                  =<< findAllIndices dets sha)

        -- Try the original operation again, with the cache now properly
        -- primed.  However, by passing True to restart we prevent this code
        -- from running the second time.
        left =<< liftIO (restart True)
