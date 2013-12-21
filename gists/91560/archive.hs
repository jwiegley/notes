fileChecksum :: FilePath -> IO BS.ByteString
fileChecksum fp = run $ ("openssl", ["sha1", "-binary", fp])

hexString :: BS.ByteString -> String
hexString =  concat . map (printf "%02x") . BS.unpack

recordChecksum :: FilePath -> IO ()
recordChecksum fp = do
  csum <- fileChecksum fp
  shell "xattr" ["-w", "checksum-sha1", hexString csum, fp]
