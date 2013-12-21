                valid <- flip runContT (return True) $ callCC $ \jump ->
                    forM ms $ \m -> do
                        mm <- getBy $ UniqueModule pid m
                        unless (isJust mm) $ jump False
