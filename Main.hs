    isLit <- lift $ runEffect $
        P.any ("> " `T.isPrefixOf`)
              (L.purely P.folds L.mconcat
                        (Text.readFile path ^. Text.lines))
