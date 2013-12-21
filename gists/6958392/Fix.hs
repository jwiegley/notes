{-# LANGUAGE OverloadedStrings #-}

module Fix where

import Control.Monad.Instances

data Fix (f :: * -> *) a = Fix (f (Fix f a)) a

newtype List a = List (Fix Maybe a)

data Free (f :: * -> *) a = Free (Either a (f (Free f a)))

instance Functor f => Functor (Free f) where
    fmap f (Free (Left a))  = Free $ Left $ f a
    fmap f (Free (Right m)) = Free $ Right $ fmap (fmap f) m

iterM :: (Monad m, Functor f) => (f (m a) -> m a) -> Free f a -> m a
iterM _ (Free (Left a))  = return a
iterM f (Free (Right m)) = f $ fmap (iterM f) m

main :: IO ()
main = print =<< iterM (\(x, y) -> print x >> y) xs
  where
    xs = Free (Right (1 :: Int, Free (Right (2, Free (Right (3, Free (Left ("Hi" :: String))))))))
