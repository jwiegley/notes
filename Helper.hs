helperPutObject :: IsolationRunnerSettings -> Text -> BL.ByteString
                -> ResourceT IO ()
helperPutObject irs path bytes =
    helperRunBase irs Helper.s3PutObject $ \tok -> do
        C.sourcePut (Cereal.put $ Helper.S3PutObjectInput path tok)
        C.sourceList (BL.toChunks bytes)
