instance MonadBaseControl IO m => MonadBaseControl IO (CanFailT m) where
  data StM (CanFailT m) a =
      StCFR { unStCFR :: StM m (CanFail a) }
  liftBaseWith f = CanFailT $ fmap Success $
      liftBaseWith $ \runInBase ->
          f (\(CanFailT sT) -> liftM StCFR . runInBase $ sT)
  restoreM = CanFailT . restoreM . unStCFR
