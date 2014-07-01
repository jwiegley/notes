module Laws where

import Control.Applicative

apply :: Applicative f => f (a -> b) -> f a -> f b
apply = (<*>)

eta :: Applicative f => a -> f a
eta = pure

compose :: (b -> c) -> (a -> b) -> a -> c
compose = (.)

-- foo :: Applicative f => f (b -> c) -> f (a -> b) -> f (a -> c)
-- foo f b = compose <$> f <*> b
--foo = apply . fmap compose
--foo = ((fmap compose) .) . apply

bar :: Applicative f => f (b -> c) -> (a -> f b) -> a -> f c
bar = compose . apply

a :: (Applicative f1, Applicative f)
  => f (f1 (b1 -> b)) -> f (f1 (a -> b1)) -> f (f1 a) -> f (f1 b)
a m m0 m1 = (apply <$> (apply <$> (fmap compose <$> m) <*> m0)) <*> m1

y :: (Applicative f1, Applicative f)
  => f (f1 (b1 -> b)) -> f (f1 (a -> b1)) -> f (f1 a) -> f (f1 b)
y m m0 m1 = ((compose <$> (apply <$> m)) <*> (apply <$> m0)) <*> m1

z :: (Applicative f1, Applicative f)
  => f (f1 (b1 -> b)) -> f (f1 (a -> b1)) -> f (f1 a) -> f (f1 b)
z m m0 m1 = apply <$> m <*> (apply <$> m0 <*> m1)

-- o = fmap apply (eta (eta compose))

-- o' :: (Applicative f1, Applicative f) => t -> f (f1 (b -> c) -> f1 ((a -> b) -> a -> c))
-- o' = eta (\h -> eta (.) <*> h)

o'' :: (Applicative f1, Applicative f) => (a -> b) -> f (f1 a -> f1 b)
o'' f = eta (apply (eta f))

p f g x = pure f <*> pure g <*> x

p' f g x = pure (f . g) <*> x

q :: (Either e y -> Either e z) -> (Either e x -> Either e y) -> Either e x -> Either e z
q = (.)

k :: (Applicative g, Applicative f)
  => ((g a -> g b1) -> (g a1 -> g b2) -> b)
  -> f (g (a -> b1)) -> f (g (a1 -> b2)) -> f b
k f x y = f <$> (apply <$> x) <*> (apply <$> y)
