safeDivide :: (Num a, Eq a, Fractional a)
           => Maybe a -> Maybe a -> Maybe a
safeDivide x y = x >>= \a -> y >>= \b ->
    if b == 0
    then Nothing
    else Just (a / b)
