{-# LANGUAGE FlexibleContexts #-}

module Teletype where

import Control.Monad
import Control.Monad.Error.Class
import System.IO.Error

data TeletypeF a b r = Get (a -> r)
                     | GetMany ((((a -> r) -> r -> r) -> r) -> r)
                     | Put b r

phi :: MonadError String m => TeletypeF String b (m r) -> m r
phi (GetMany k) = forever $ do
    s <- getLine
    if s == "error"
        then throwError (userError "User signalled an error")
        else if s == "end"
             then k $ \_ e -> e
             else k $ \f _ -> f s
