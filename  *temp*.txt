-- | This function requires a specific source span, to identify a single
--   identifier.  We cannot return multiple identifiers within a larger range.
typeInfoForRange' :: IsolationRunnerState
                  -> ProjectFileRange
                  -> ResourceT IO (ProjectResult [(SourceSpan, SpanInfo)])
typeInfoForRange' irst ProjectFileRange{..} =
    withProjManager "typeInfoForRange"
        irst pfrProjectName LoadingManager $ \_block mgr -> liftIO $ do
            gif <- getSpanInfo (mgrSession mgr)
            return . ProjectResult $ gif pfrModuleName
                (SourceSpan (unpack pfrFilePath)
                 pfrStartLine pfrStartCol pfrEndLine pfrEndCol)
            -- egif <- tryAny $ getSpanInfo (mgrSession mgr)
            -- return . ProjectResult $ case egif of
            --     Left _    -> []
            --     Right gif -> gif pfrModuleName
            --                      (SourceSpan (unpack pfrFilePath)
            --                       pfrStartLine pfrStartCol pfrEndLine pfrEndCol)
