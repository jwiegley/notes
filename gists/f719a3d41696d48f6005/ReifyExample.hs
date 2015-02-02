{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

module ReifyExample where

import Data.Reflection
import Debug.Trace

data Foo a b = Foo b deriving (Show, Functor)

data Binder m = Binder
    { getBinder :: forall a b. Monad m => m a -> (a -> m b) -> m b }

instance Reifies a (Binder (Foo a)) => Monad (Foo a) where
    return  = Foo
    x >>= f = getBinder (reflect (undefined :: proxy a)) x f

instance Reifies Int (Binder (Foo Int)) where
    reflect _ = Binder $ trace "intBind" $ \(Foo m) f -> f m

instance Reifies Float (Binder (Foo Float)) where
    reflect _ = Binder $ trace "floatBind" $ \(Foo m) f -> f m

main :: IO ()
main = do
    let x = Foo 10 :: Foo Int Int
        y = Foo 20 :: Foo Float Int
    print $ reify undefined $ \_ -> x >>= return . (+1)
    print $ reify undefined $ \_ -> y >>= return . (+1)
