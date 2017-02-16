module Zips where

import Control.Applicative
import Control.Arrow

zipWith :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
zipWith = liftA2

zip :: Applicative f => f a -> f b -> f (a, b)
zip = liftA2 (,)

zap :: Applicative f => f (a -> b) -> f a -> f b
zap = (<*>)

unzip :: Functor f => f (a, b) -> (f a, f b)
unzip = fmap fst &&& fmap snd
