data Burrito a = Burrito (Burrito a)
instance Monad Burrito where
    return x = Burrito (return x)
    Burrito m >>= f = Burrito (m >>= f)
