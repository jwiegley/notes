data EventStream

instance Accept EventStream where
   contentType _ = "text" // "event-stream"

instance MimeRender EventStream ByteString where
   mimeRender _ val = fromStrict ("data:" <> val <> "\n")
