headFile :: Manager -> Text -> Text -> Text -> Text -> ResourceT IO Bool
headFile manager bucket access secret filepath = do
  let req    = headObject bucket filepath
      creds  = Credentials { accessKeyID     = E.encodeUtf8 access
                           , secretAccessKey = E.encodeUtf8 secret }
  res <- aws (Configuration Timestamp creds $ defaultLog Error)
            defServiceConfig manager req
  return $ case readResponse res of
    Nothing -> False
    Just _  -> True
