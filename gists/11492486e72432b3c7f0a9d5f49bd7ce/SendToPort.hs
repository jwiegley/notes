sendToPort :: MonadIO m
           => ByteString
           -> HostName
           -> PortNumber
           -> m ByteString
sendToPort content host port = liftIO $
    connect host (show port) $ \(sock, _remoteAddr) -> do
        send sock content
        shutdown sock ShutdownSend
        fromMaybe "" <$> recv sock 8192
