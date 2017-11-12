main = evalStateT (runEffect $ stream >-> P.stdout)
                  (gregorian # YearMonthDay 1970 1 1, Nothing)
  where
    stream = for (void (P.stdin ^. P.decoded)
                    >-> P.mapFoldable packetSegments) $ \s -> do
        lift $ observe (segmentData s)
        lift . lift $ hPutStr stderr $ "Sending segment: " ++ show s ++ "\n"
        P.encode s