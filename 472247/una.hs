extractByTemp :: B.ByteString   -- output to write to temp
                 -> String      -- the temporary file extension
                 -> (Extraction -> IO ExtractionResult)
                                -- function to handle the new temp file
                 -> IO ExtractionResult
extractByTemp ds ext fn = do
  dir <- workingDirectory
  (path, handle) <- openBinaryTempFile dir ("file" ++ ext)

  loud <- isLoud
  when loud $ putStrLn $ "> " ++ path

  B.hPut handle ds
  hFlush handle
  -- unzip does not support reading from standard input, so we must write the
  -- data out to a temporary file in order to continue.
  (x,m) <- fn (FileName path)
  hClose handle
  return (x, do removeFile path; m)
