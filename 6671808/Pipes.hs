-- | Return either the final element returned from a conduit sink, or the next
--   element yielded by that conduit along with another conduit representing
--   its remainder.
next :: Monad m => ConduitM i i m r -> m (Either r (i, ConduitM i i m r))
next = go
  where
    go p = case unConduitM p of
        NeedInput  _ _    -> absurd undefined
        HaveOutput fu _ a -> return (Right (a, ConduitM fu))
        PipeM      m      -> m >>= go . ConduitM
        Done       r      -> return (Left r)
        Leftover   fu a   -> return (Right (a, ConduitM fu))
