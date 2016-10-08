cocataM :: Monad m => (a -> Either b (Operator b) -> m b) -> b -> Cofree Operator a -> m b
cocataM k z (x :< Atom _) = k x (Left z)
cocataM k z (x :< xs) = k x . Right =<< traverse (cocataM k z) xs
