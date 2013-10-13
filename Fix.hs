{-# LANGUAGE OverloadedStrings #-}

module Fix where

import Control.Monad.Instances
import Data.Functor.Compose

newtype Fix (f :: * -> *) = Fix { unFix :: f (Fix f) }

newtype List = List (Fix Maybe)

--type Free2 f = Fix (Compose (Compose f) Either)

type Free f a = Fix (Compose (Either a) f)

-- instance Functor f => Functor (Fix (Compose (Either a) f)) where
--     fmap f (Fix (Compose (Left a)))  = Fix $ Compose $ Left $ f a
--     fmap f (Fix (Compose (Right m))) = Fix $ Right $ fmap (fmap f) m

iterM :: (Monad m, Functor f) => (f (m a) -> m a) -> Free f a -> m a
iterM _  (Fix (Compose (Left a)))  = return a
iterM f  (Fix (Compose (Right m))) = f $ fmap (iterM f) m

main :: IO ()
main = print =<< iterM (\(x, y) -> print x >> y) xs
  where
    xs = Fix (Compose (Right (1 :: Int, Fix (Compose (Right (2, Fix (Compose (Right (3, Fix (Compose (Left ("Hi" :: String))))))))))))
