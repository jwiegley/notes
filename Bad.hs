{-# LANGUAGE OverloadedStrings #-}

module Bad where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid

data Bad a = Bad (Bad a -> a)

getFun :: Bad a -> Bad a -> a
getFun (Bad f) = f

omega :: Bad a -> a
omega f = getFun f f

loop :: Bad a
loop = omega (Bad omega)
