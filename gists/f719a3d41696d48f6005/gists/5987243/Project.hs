                minvalidPath <- lift $ runMaybeT $ msum $ flip map ms $
                    \mn -> MaybeT $ do
                       mm <- getBy $ UniqueModule pid mn
                       return $ maybe (Just ()) (const Nothing) mm
