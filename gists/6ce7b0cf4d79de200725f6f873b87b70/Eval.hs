streamValues :: MonadVar m => NValue m -> Stream (NValueF m) m ()
streamValues x = void $ yields $ flip fmap x $ \case
    NThunk (Left v) -> streamValues v
    NThunk v -> effect (streamValues <$> forceThunk v)
