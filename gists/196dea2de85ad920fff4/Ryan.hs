{-# LANGUAGE ExistentialQuantification #-}

import Data.Functor.Rep

data Behavior a = Behavior
data Event a = Event

data Dynamic t a = forall f x. (Functor f, Representable f)
    => Dynamic (Behavior (Rep f)) (Event (Rep f)) (f a)

instance Functor (Dynamic t) where
    fmap f (Dynamic k xs h) = Dynamic k xs (map f h)
