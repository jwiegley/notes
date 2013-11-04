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
    { runLgRepository :: IdentityT m a
    }
    deriving (Functor, Applicative, Monad, MonadIO)

instance MonadLogger m => MonadLogger (LgRepository m) where
    monadLoggerLog a b c d = LgRepository $ monadLoggerLog a b c d

instance (MonadIO m, MonadLogger (l m)) => Repository (LgRepository (l m)) where
    data Foo (LgRepository (l m)) = LgFooLog Int
    act (LgFooLog x) = $(logDebug) $ "This is from logDebug: " <> pack (show x)

instance MonadIO m => Repository (LgRepository m) where
    data Foo (LgRepository m) = LgFoo Float
    act (LgFoo x) = liftIO $ putStrLn $ "This is from putStrLn: " ++ show x

main :: IO ()
main = do
    runIdentityT (runLgRepository $ act (LgFoo 1.0))
    runNoLoggingT $ runIdentityT (runLgRepository $ act (LgFooLog 10))
    runStdoutLoggingT $ runIdentityT (runLgRepository $ act (LgFooLog 20))
