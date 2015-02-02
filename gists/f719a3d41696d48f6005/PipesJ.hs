module Pipes where

data ProxyF a' a b' b m p
    = Request a' (a  -> p)
    | Respond b  (b' -> p)
    | M          (m p)

instance Functor m => Functor (ProxyF a' a b' b m) where
    fmap f (Request a r) = Request a (fmap f r)
    fmap f (Respond b r) = Respond b (fmap f r)
    fmap f (M m)         = M (fmap f m)

data Free f a = Pure a | Free (f (Free f a))

-- By using the Free monad construction, Proxy automatically becomes an
-- Applicative and Monad.
type Proxy a' a b' b m = Free (ProxyF a' a b' b m)

newtype X = X X

absurd :: X -> a
absurd a = a `seq` spin a where
   spin (X b) = spin b

runEffect :: Monad m => Proxy X () () X m r -> m r
runEffect = go
  where
    go p = case p of
        Pure r -> return r
        Free (M m) -> m >>= go
        Free (Request v _) -> absurd v
        Free (Respond v _) -> absurd v
