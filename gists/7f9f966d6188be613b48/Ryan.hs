{-# LANGUAGE ExistentialQuantification #-}

data Dynamic t a = forall x. Dynamic (t -> x) [(t, x)] (x -> a)

instance Functor (Dynamic t) where
    fmap f (Dynamic k xs h) = Dynamic k xs (map f h)
