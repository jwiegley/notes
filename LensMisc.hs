module LensMisc where

import Control.Lens
import Data.Char

orded :: Iso' Char Int
orded = dimap ord (fmap chr)
