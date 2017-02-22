module Ran where

import Data.Functor.Kan.Ran
import Data.Maybe

ranaway :: Ran Maybe [] a
ranaway = toRan go []
  where
    go :: [Maybe a] -> [a]
    go x = x >>= maybeToList
