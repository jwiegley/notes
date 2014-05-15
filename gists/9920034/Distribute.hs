dist :: Distributive f => (a -> f b) -> f (a -> b)
dist f = distribute f
