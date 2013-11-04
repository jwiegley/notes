{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module MonadLogger where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Logger
import Control.Monad.Trans.Identity

class Repository m where
    act :: m ()

newtype LgRepository m a = LgRepository
    { runLgRepository :: IdentityT m a
    }
    deriving (Functor, Applicative, Monad, MonadIO)

instance MonadLogger m => MonadLogger (LgRepository m) where
    monadLoggerLog a b c d = LgRepository $ monadLoggerLog a b c d

instance (MonadIO m, MonadLogger m) => Repository (LgRepository m) where
    act = $(logDebug) "This is from logDebug"

main :: IO ()
main = do
    runIdentityT (runLgRepository act)
    runNoLoggingT $ runIdentityT (runLgRepository act)
    runStdoutLoggingT $ runIdentityT (runLgRepository act)
