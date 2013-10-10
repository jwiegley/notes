{-# OPTIONS_GHC -fno-warn-orphans #-}

module Freet where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Data.Foldable
import Data.Traversable

data ListT m a = Nil | Cons a (m (ListT m a))

foldListT :: (MonadIO m, Show a) => (a -> m ()) -> ListT m a -> m ()
foldListT _ Nil = return ()
foldListT f (Cons x m) = do
    f x
    xs <- m
    foldListT f xs

data FreeT f m a = Pure a | Free (m (f (FreeT f m a)))

instance Foldable ((,) e) where
    foldMap f (_,a) = f a

instance Traversable ((,) e) where
    traverse f (e,a) = (,) <$> pure e <*> f a

foldFreeT :: (Traversable f, Applicative m, Functor m, MonadIO m)
           => (f (FreeT f m a) -> m a) -> FreeT f m a -> m a
foldFreeT _ (Pure a) = return a
foldFreeT f (Free m) = do
    val <- m
    x <- f val
    void $ traverse (foldFreeT f) val
    return x

main :: IO ()
main = do
    foldListT print listTdata
    foldFreeT (print . fst) freeTdata
  where
    listTdata =
        Cons (10 :: Int)
             (return (Cons 20
                           (return (Cons 30
                                         (return Nil)))))
    freeTdata =
        Free (return (10 :: Int,
                      Free (return (20,
                                    Free (return (30,
                                                  Pure ()))))))
