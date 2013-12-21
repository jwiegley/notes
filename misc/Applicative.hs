module Main where

data Identity a = Identity a

instance Functor Identity where
    fmap f (Identity x) = Identity (f x)

class Functor f => Applicative f where {
    unit :: f ();
    times :: f a -> f b -> f (a,b)
}

instance Applicative Identity where
    unit = Identity ()
    times (Identity x) (Identity y) = Identity (x,y)

pure :: Applicative f => a -> f a
pure x = fmap (const x) unit

(<*>) :: Applicative f => f (a -> b) -> f a -> f b
f <*> x = fmap (\(f',x') -> f' x') (f `times` x)

-- TODO: Prove that the laws for unit and times hold for pure and <*>

{-

identity      unit `times` x = id `times` x
composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
homomorphism  pure f <*> pure x = pure (f x)
interchange   u <*> pure y = pure ($ y) <*> u

-}

{-

identity      pure id <*> v = v
composition   pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
homomorphism  pure f <*> pure x = pure (f x)
interchange   u <*> pure y = pure ($ y) <*> u

-}

main = undefined
