{-# LANGUAGE OverloadedStrings #-}

module Distribute where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.State
import Data.Distributive
import Data.Maybe
import Data.Monoid

instance Distributive g => Distributive (StateT e g) where
  distribute a = StateT $ \s -> collect (flip runStateT s) a
