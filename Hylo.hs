{-# LANGUAGE DeriveFunctor #-}

module Hylo where

data Identity a = Identity { runIdentity :: a } deriving Functor

newtype Compose f g a = Compose { getCompose :: f (g a) }

newtype Fix f = Fix { unFix :: f (Fix f) }

newtype Free f a = Free { runFree :: Fix (Compose (Either a) f)}

instance Functor f => Functor (Free f) where
    fmap f (Free h) = Free (go h) where
        go (Fix (Compose x)) = Fix (Compose (k x)) where
            k (Left a)  = Left (f a)
            k (Right n) = Right (fmap go n)

cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

-- | Anamorphism or generic function unfold.
ana :: Functor f => (a -> f a) -> a -> Fix f
ana f = Fix . fmap (ana f) . f

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo phi psi = cata phi . ana psi

main :: IO ()
main = do
    let phi = (\(Free (Fix (Compose (Left x)))) -> x)
                :: Free Identity Int -> Int
        psi = (Free . Fix . Compose . Left)
                :: Int -> Free Identity Int
    print $ hylo phi psi 10
