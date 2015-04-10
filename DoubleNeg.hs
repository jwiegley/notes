fmap' :: (a -> b) -> ((a -> Int) -> Int) -> ((b -> Int) -> Int)
fmap' f g k = g (k . f)
