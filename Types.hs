instance MonadBaseControl IO (API.CanFailT RunnerIO) where
  data StM (API.CanFailT RunnerIO) a =
      StCFR { unStCFR :: StM RunnerIO (API.CanFail a) }
  liftBaseWith f = API.CanFailT $ fmap API.Success $
      liftBaseWith $ \runInBase ->
          f (\(API.CanFailT sT) -> liftM StCFR . runInBase $ sT)
  restoreM = API.CanFailT . restoreM . unStCFR

