module RoseFree where

import Control.Monad

data Free f a
    = Pure a
    | Impure (f (Free f a))

data RoseFree f a
    = RosePure a
    | RoseImpure (f [RoseFree f a])
