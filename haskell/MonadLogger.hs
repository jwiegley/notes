{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MonadLogger where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Logger
import Control.Monad.Trans.Identity
import Data.Monoid
import Data.Text

class Repository m where
    data Foo m :: *
    act :: Foo m -> m ()

newtype LgRepository m a = LgRepository
    { runLgRepositoryLog :: IdentityT m a
    }
    deriving (Functor, Applicative, Monad, MonadIO)

runLgRepository :: LgRepository (NoLoggingT m) a -> m a
runLgRepository = runNoLoggingT . runIdentityT . runLgRepositoryLog

instance MonadLogger m => MonadLogger (LgRepository m) where
    monadLoggerLog a b c d = LgRepository $ monadLoggerLog a b c d

instance (MonadIO m, MonadLogger m) => Repository (LgRepository m) where
    data Foo (LgRepository m) = LgFoo Int
    act (LgFoo x) = $(logDebug) $ "This is from logDebug: " <> pack (show x)

main :: IO ()
main = do
    runLgRepository $ act (LgFoo 5)
    runNoLoggingT $ runIdentityT (runLgRepositoryLog $ act (LgFoo 10))
    runStdoutLoggingT $ runIdentityT (runLgRepositoryLog $ act (LgFoo 20))
