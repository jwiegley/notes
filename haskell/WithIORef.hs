module WithIORef where

import Control.Monad.State
import Data.IORef
import Data.Tuple

withIORef :: IORef a -> State a b -> IO b
withIORef ref action = atomicModifyIORef ref (swap . runState action)
