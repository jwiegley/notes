{-# LANGUAGE GeneralizedNewtypeDeriving #-}

import Control.Monad.IO.Class

data Request = Request
data Response = Response

class MonadHttp m where
    http :: Request -> m Response

newtype MockHttp a = MockHttp { runMockHttp :: IO a } deriving Monad

instance MonadIO MockHttp where
    liftIO = MockHttp

instance MonadHttp IO where
    http = undefined {- do some real stuff here -}

instance MonadHttp MockHttp where
    http = undefined {- do some real stuff here -}

runHttp :: IO a -> IO a
runHttp = id

main = do
    runHttp $ http Request
    runMockHttp $ http Request
