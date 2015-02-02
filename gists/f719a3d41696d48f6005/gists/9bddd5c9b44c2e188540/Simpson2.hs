module Simpson2 where

f :: (forall a. Maybe a) -> Maybe b
f = undefined

g :: Maybe a -> Maybe b
g = undefined

h :: (forall a. Maybe a) -> Maybe b
-- h x = g (f x)
h = g . f
