{-# LANGUAGE FlexibleInstances #-}

module UnitCategory where

import Control.Category

data Const2 c a b = Const2 c

instance Category (Const2 ()) where
    id = Const2 ()
    f . g = Const2 ()
