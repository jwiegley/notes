main = flip evalStateT (gregorian # YearMonthDay 1970 1 1, Nothing) $ do
    bytes <- lift $ BS.hGetContents stdin
    go bytes
  where
    go :: ByteString -> StateT (Day, Maybe UTCTime) IO ()
    go "" = return ()
    go bytes = case decodeOrFail bytes of
        Left (_bs, _off, err) ->
            error $ "Error reading packet: " ++ err
        Right (bs, _off, Packet {..}) -> do
            forM_ packetSegments $ \s -> do
                observe (segmentData s)
                lift $ do
                    hPutStr stderr $ "Sending segment: " ++ show s ++ "\n"
                    BS.hPutStr stdout $ encode s
            go bs