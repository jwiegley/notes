{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ScopedTypeVariables #-}

module FreeBase where

import Control.Monad.Trans.Control
import Control.Monad.Trans.Free
import Control.Monad.Base

instance (MonadBase b m, Functor f) => MonadBase b (FreeT f m) where
    liftBase = liftBaseDefault

instance (MonadBaseControl b m, Functor f)
         => MonadBaseControl b (FreeT f m) where
    type StM (FreeT f m) a = StM m (FreeF f a (FreeT f m a))
    liftBaseWith f =
        FreeT $ fmap Pure $ liftBaseWith $ \runInBase ->
            f $ \k -> runInBase $ runFreeT k
    restoreM = FreeT . restoreM

data Pair a = Pair a a deriving Functor

foo :: forall m. MonadBaseControl IO m => FreeT Pair m Int
foo = do
    liftBase $ putStrLn "foo.1"
    y <- FreeT $ return $ Free $ Pair alpha beta
    liftBase $ putStrLn "foo.10"
    return y

alpha :: forall m. MonadBaseControl IO m => FreeT Pair m Int
alpha = do
    liftBase $ putStrLn "foo.2"
    FreeT $ return $ Pure (10 :: Int)

beta :: forall m. MonadBaseControl IO m => FreeT Pair m Int
beta = do
    liftBase $ putStrLn "foo.3"
    x' <- liftBaseWith $ \runInBase -> do
        putStrLn "foo.4"
        x <- runInBase $
             FreeT $ return $ Free $
               Pair (FreeT $ do liftBase $ putStrLn "foo.5"
                                return $ Pure (20 :: Int))
                    (FreeT $ do liftBase $ putStrLn "foo.6"
                                return $ Pure (30 :: Int))
        -- We run into a problem here, because we're unable to capture the
        -- fact that the structure of the preceding Free construction is to
        -- bind these following statement at each branch point; instead, we
        -- are forced to reduce the construction early. Solving would mean
        -- packaging up the parts of this computation that occurred within the
        -- base monad (under 'liftBaseWith'), and recording those as if they
        -- had happened with 'liftBase' instead.
        putStrLn "foo.7"
        return x
    liftBase $ putStrLn "foo.8"
    x'' <- restoreM x'
    liftBase $ putStrLn "foo.9"
    return x''

foo' :: forall m. MonadBaseControl IO m => FreeT Pair m Int
foo' = do
    liftBase $ putStrLn "foo'.1"
    y <- FreeT $ return $ Free $ Pair alpha' beta'
    liftBase $ putStrLn "foo'.10"
    return y

alpha' :: forall m. MonadBaseControl IO m => FreeT Pair m Int
alpha' = do
    liftBase $ putStrLn "foo'.2"
    FreeT $ return $ Pure (10 :: Int)

beta' :: forall m. MonadBaseControl IO m => FreeT Pair m Int
beta' = do
    liftBase $ putStrLn "foo'.3"
    x' <- do
        liftBase $ putStrLn "foo'.4"
        x <- FreeT $ return $ Free $
             Pair (FreeT $ do liftBase $ putStrLn "foo'.5"
                              return $ Pure (20 :: Int))
                  (FreeT $ do liftBase $ putStrLn "foo'.6"
                              return $ Pure (30 :: Int))
        liftBase $ putStrLn "foo'.7"
        return x
    liftBase $ putStrLn "foo'.8"
    liftBase $ putStrLn "foo'.9"
    return x'

main :: IO ()
main = do
    iterT (\(Pair a b) -> a >> b) foo' >>= print
    iterT (\(Pair a b) -> a >> b) foo  >>= print
