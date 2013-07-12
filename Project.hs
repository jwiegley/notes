                haveInvalid <- forWithBreakM (return False) $ \exit m -> do
                    mm <- getBy $ UniqueModule pid m
                    when (isNothing mm) $ exit True
