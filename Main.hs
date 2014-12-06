-- | Start an external ghci process, run a computation with access to
--   it, and finally stop the process.
ghciProcess :: (MonadCatch m, MonadSafe m)
            => FilePath -> Pipe (GhciInput, String) GhciLine m ()
ghciProcess path = do
    isLit <- lift $ runEffect $
        P.any ("> " `T.isPrefixOf`)
              (L.purely P.folds L.mconcat
                        (Text.readFile path ^. Text.lines))
    for cat $ \(input, str) -> do
        let cmd = ["ghci", "-v0", "-ignore-dot-ghci"] ++ [ path | isLit ]
        P.parsed ghciParser
            (Text.decodeUtf8
                (Text.encodeUtf8 (T.pack str)
                     >-> P.map Just
                     >-> pipeCmd' (unwords cmd)))
            >-> P.map (GhciLine input . OK)
        return ()
  where
    magic' = T.pack magic

    ghciParser = manyTill anyChar (try (string magic'))
              *> manyTill anyChar (try (string magic'))
              <* takeLazyText
