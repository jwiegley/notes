{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Proof where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.Maybe
import Data.Monoid
import Data.Promotion.Prelude
import Data.Promotion.Prelude.Bool
import Data.Singletons.Prelude
import GHC.TypeLits

proof :: Sing (0 :< 1); proof = STrue

main :: IO ()
main = undefined
