data EventStream

instance Accept EventStream where
   contentType _ = "text" // "event-stream"

instance MimeRender EventStream ByteString where
   mimeRender _ val = fromStrict ("data:" <> val <> "\n")

runUI
  :: forall m. MonadUnliftIO m
  => MonadThrow m
  => MonadLogger m
  => MonadReader Config m
  => Port
  -> TQueue ChainUserInput
  -> TChan (Double, Block'')
  -> m ()
runUI port qInUser qInBlocks = withRunInIO $ \runInIO ->
  run port $
    serve servantAPI $
      hoistServer servantAPI
        (Handler . lift . runInIO :: forall x. m x -> Handler x)
        (ui qInUser qInBlocks)

servantAPI :: Proxy ClientAPI
servantAPI = Proxy
