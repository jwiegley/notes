{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Laarhoven where

import Control.Lens

class Laarhoven a b where
  type Rest a :: *
  project :: a -> (Rest a, b)
  combine :: Rest a -> b -> a

main = (Right 10, Left 20) & _1._Left .~ 2
                           & _2._Left .~ 2
