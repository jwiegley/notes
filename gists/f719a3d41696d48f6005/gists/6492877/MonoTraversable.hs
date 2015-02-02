class MonoMonad c where
    mreturn :: Element c -> c
    mbind :: c -> (Element c -> c) -> c
instance Monad m => MonoMonad (m a) where
    mreturn = return
    mbind = (>>=)
instance MonoMonad S.ByteString where
    mreturn = S.singleton
    mbind = flip S.concatMap
