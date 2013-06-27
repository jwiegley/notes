{-# LANGUAGE RankNTypes #-}

module Initial where

data Initial i = Initial (forall x. i -> x)

instance Functor Initial where
    fmap f (Initial g) = Initial (g . f)
