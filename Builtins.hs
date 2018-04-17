foldl'_ :: forall e m. MonadBuiltins e m
        => m (NValue m) -> m (NValue m) -> m (NValue m) -> m (NValue m)
foldl'_ f z = fromValue @[NThunk m] >=> foldl' go z
  where
    go :: m (NValue m) -> NThunk m -> m (NValue m)
    go b a = force a $ \a' -> call2 f (pure a') b
