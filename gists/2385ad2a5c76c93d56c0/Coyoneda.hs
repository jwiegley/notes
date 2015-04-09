import Data.Profunctor

data Coyoneda f a b = Coyoneda (a -> b) (f b)

instance Functor f => Profunctor (Coyoneda f) where
    dimap f g (Coyoneda k x) = Coyoneda (g . k . f) (fmap g x)
