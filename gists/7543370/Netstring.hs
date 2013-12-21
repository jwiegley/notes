recvNetstring :: Monad m
              => Sink ByteString m a -> ConduitM ByteString Void m a
recvNetstring bsink = do
    len <- CB.takeWhile isDigit' =$ CL.consume
    colon <- CB.head
    when (colon == Just (fromIntegral (ord ':'))) $ do
        m <- CB.take $ read (BC.unpack (B.concat len))
        lift $ sourceLbs m $$ bsink
  where
    isDigit' w = w >= 48 && w <= 57
