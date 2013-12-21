lazyFromStrictB :: B.ByteString -> BL.ByteString
lazyFromStrictB = flip BLI.chunk BLI.Empty

lazyToStrictB :: BL.ByteString -> B.ByteString
lazyToStrictB lb = BI.unsafeCreate len $ go lb
  where
    len = BLI.foldlChunks (\l sb -> l + B.length sb) 0 lb

    go  BLI.Empty                   _   = return ()
    go (BLI.Chunk (BI.PS fp s l) r) ptr =
        withForeignPtr fp $ \p -> do
            BI.memcpy ptr (p `plusPtr` s) (fromIntegral l)
            go r (ptr `plusPtr` l)
