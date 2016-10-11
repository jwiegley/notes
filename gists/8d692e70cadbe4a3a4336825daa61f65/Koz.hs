cocataM :: (Monad m, Traversable f) => (a -> f b -> m b) -> Cofree f a -> m b
cocataM k (x :< xs) = k x =<< traverse (cocataM k) xs