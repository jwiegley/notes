module Pipes where

data Free f a = Return a | Free (f (Free f a))

data ProxyF a' a b' b m p
    = Request a' (a  -> p)
    | Respond b  (b' -> p)
    | M          (m p)

type Proxy a' a b' b m = Free (ProxyF a' a b' b m)
