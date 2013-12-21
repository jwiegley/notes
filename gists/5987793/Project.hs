                elem <- firstM
                    (fmap isNothing . getBy . UniqueModule pid)
                    (elems revModMap)
                case elem of
                    Just _ -> do
                        lift emptyProject
                        loadWithInvalidSettings tree
                    Nothing ->
                        lift $ update pid [ProjectInvalidSettings =. False]
