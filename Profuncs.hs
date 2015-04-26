module Profuncs where

import Control.Applicative
import Data.Profunctor
import Data.Map

instance Profunctor Map where
    dimap f g m =
        Data.Map.foldrWithKey
            (\k x m -> Data.Map.insert k (g x) m) Data.Map.empty m
