odbS3BackendReadCallback :: F'git_odb_backend_read_callback
odbS3BackendReadCallback data_p len_p type_p be oid = do
    str <- oidToStr oid
    wrap ("odbS3BackendReadCallback " ++ str)
        (go False)
        (return (-1))
  where
    go = fix $ \restart seen -> do
