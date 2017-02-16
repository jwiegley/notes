{-# LANGUAGE OverloadedStrings #-}

module Produce where

import Data.ByteString
import Pipes
import Pipes.Prelude

axman6 :: Monad m => Producer ByteString m () -> Producer ByteString m ()
axman6 src = for src yield
