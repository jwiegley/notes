{-# LANGUAGE FlexibleContexts #-}

import Data.Conduit
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.IO.Class
import qualified Data.Conduit.List as CL

run :: Monad m => Sink a m b -> StateT (ResumableSource m a) m b
run consumer = do
  src <- get
  (s,r) <- lift $ src $$++ consumer
  put s
  return r

main :: IO ()
main = do
    let someSource = undefined :: ResumableSource m a
    xs <- evalStateT (run $ CL.take 3) someSource
    return ()
