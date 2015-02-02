newtype Query a = Query (Free (forall k v. Lookup k v) a)

instance Functor Query where
    fmap f (Query (Pure x)) = Query (Pure (f x))
    fmap f (Query (Free (Lookup k h))) = Query (Free (Lookup k (f . h)))
