{-# LANGUAGE OverloadedStrings #-}

module LensMap where

import Control.Applicative
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Trans.RWS
import Data.Map
import Data.Maybe
import Data.Monoid

getTopLevelName :: String -> RWS (Map String String) (Map String String) Int String
getTopLevelName s =
  do m <- use (at s)
     case m of
      Nothing -> do n <- uniqName s
                    tell $ Data.Map.singleton s n
                    return n
      Just n -> return n
  where
    uniqName = undefined
