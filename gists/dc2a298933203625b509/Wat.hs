{-# LANGUAGE RankNTypes #-}

module Wat where

import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader
import Control.Monad.ST
import Data.STRef

data Foo = Foo
data Bar = Bar

newtype Wat a = Wat { runWat :: forall s. WriterT Foo (ReaderT (STRef s Bar) (ST s)) a }

doWat :: Wat t -> Bar -> Foo
doWat (Wat a) x = runST $ do
    var <- newSTRef x
    runReaderT (execWriterT a) var
