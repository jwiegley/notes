module Foo where

import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import Control.Monad.Morph
import Control.Monad.STM

data ServantErr = ServantErr
data MyStore = MyStore

foo :: ExceptT ServantErr STM Int -> ReaderT MyStore (ExceptT ServantErr IO) Int
foo = lift . hoist atomically
