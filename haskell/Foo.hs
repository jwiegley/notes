{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TupleSections #-}

module Foo where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

class Foo a b | a -> b

newtype StateT s m a = StateT { runStateT :: s -> m (a, s) }

instance MonadTrans (StateT s) where
    lift x = StateT $ \s -> (,s) <$> x

    case RewriteFxRewriteFx.findCycles model of
        [] -> pure ()
        cycles -> do
          let err = unlines (map showCycle cycles)
              showCycle [name] = "  " ++ show name ++ " (self-referential)"
              showCycle names = "  " ++ intercalate " -> " (map show names)
          fail $ "Cycles found after equality saturation: " ++ err

    forM_ (RewriteFxRewriteFx.findCycles model) $ \cycle -> do
          let showCycle [name] = "  " ++ show name ++ " (self-referential)"
              showCycle names = "  " ++ intercalate " -> " (map show names)
          fail $ "Cycles found after equality saturation: " ++ showCycle cycle
