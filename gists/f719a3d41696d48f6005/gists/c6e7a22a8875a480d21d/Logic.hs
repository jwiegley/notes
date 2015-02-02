module Logic where

newtype LogicA r m a = LogicA ((a -> m r -> m r) -> m r -> m r)
newtype LogicB r m a = LogicB ((a ->   r -> m r) ->   r -> m r)

fromLogic :: Monad m => LogicA r m a -> LogicB r m a
fromLogic (LogicA await) = LogicB $ \yield z ->
    flip await (return z) $ \x r -> r >>= yield x

toLogic :: Monad m => LogicB r m a -> LogicA r m a
toLogic (LogicB await) = LogicA $ \yield mz -> do
    z <- mz
    flip await z $ \x r -> yield x (return r)
