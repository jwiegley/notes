module Hylo where

newtype Fix f = Fix { unFix :: f (Fix f) }

cata :: Functor f => (f a -> a) -> (Fix f -> a)
cata f = f . fmap (cata f) . unFix

-- | Anamorphism or generic function unfold.
ana :: Functor f => (a -> f a) -> (a -> Fix f)
ana f = Fix . fmap (ana f) . f

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo phi psi = cata phi . ana psi

main = do
    print $ hylo (\(Left x) -> x) (\x -> Left x) 10
