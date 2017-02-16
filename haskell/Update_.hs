{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Update where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.RWS.Class
import Data.Functor.Identity
import Data.Maybe
import Data.Monoid.Action
import Data.Monoid.Coproduct
import Data.Monoid (Last(..))
import Data.Semigroup hiding (Last(..))

data UpdateT s p m a = UpdateT { runUpdateT :: s -> m (p, a) }

type Update s p = UpdateT s p Identity

instance (MonadIO m, Monoid p, Action p s) => MonadIO (UpdateT s p m) where
    liftIO m = UpdateT $ \_ -> do
        a <- liftIO m
        return (mempty, a)

instance Monad m => Functor (UpdateT s p m) where
    fmap f (UpdateT g) = UpdateT $ fmap (liftM (fmap f)) g

instance (Monad m, Monoid p, Action p s)
         => Applicative (UpdateT s p m) where
    pure = return
    UpdateT f <*> UpdateT x = UpdateT $ \s -> do
        (p, f')  <- f s
        (p', x') <- x (p `act` s)
        return (p `mappend` p', f' x')

instance (Monad m, Monoid p, Action p s) => Monad (UpdateT s p m) where
    return a = UpdateT $ \_ -> return (mempty, a)
    m >>= f = join' (fmap f m)

-- This implementation is from the slides at
--   http://homepages.inf.ed.ac.uk/s1225336/talks/types13.pdf
join' :: (Monad m, Monoid p, Action p s)
      => UpdateT s p m (UpdateT s p m a) -> UpdateT s p m a
join' (UpdateT f) = UpdateT $ \s -> do
    (p, UpdateT g) <- f s
    (p', x) <- g (p `act` s)
    return (p `mappend` p', x)

newtype ReaderT r m a = ReaderT (UpdateT r () m a)
    deriving (Functor, Applicative, Monad, MonadIO)

instance Monad m => MonadReader r (ReaderT r m) where
    ask = ReaderT . UpdateT $ \r -> return ((), r)

runReaderT :: Monad m => ReaderT r m a -> r -> m a
runReaderT (ReaderT (UpdateT f)) r = snd `liftM` f r

newtype WriterT w m a = WriterT (UpdateT () (Trivial w) m a)
    deriving (Functor, Applicative, Monad, MonadIO)

instance (Monad m, Monoid w) => MonadWriter w (WriterT w m) where
    tell x = WriterT . UpdateT $ \() -> return (Trivial x, ())

runWriterT :: (Monad m, Monoid w) => WriterT w m a -> m (w, a)
runWriterT (WriterT (UpdateT f)) = first getTrivial `liftM` f mempty

newtype Trivial a = Trivial { getTrivial :: a } deriving Monoid

instance Action (Trivial a) b where
    act _ b = b

instance Action (Last s) s where
    act (Last s) s' = fromMaybe s' s

instance Action (Last s) (a, s) where
    act (Last s) (a, s') = (a, fromMaybe s' s)

newtype StateT s m a = StateT (UpdateT s (Last s) m a)
    deriving (Functor, Applicative, Monad, MonadIO)

instance Monad m => MonadState s (StateT s m) where
    get   = StateT . UpdateT $ \s -> return (mempty, s)
    put s = StateT . UpdateT $ \_ -> return (Last (Just s), ())

runStateT :: Monad m => StateT s m a -> s -> m (s, a)
runStateT (StateT (UpdateT f)) s = first (`act` s) `liftM` f s

newtype RWST r w s m a = RWST (UpdateT (r, s) (Trivial w :+: Last s) m a)
    deriving (Functor, Applicative, Monad, MonadIO)

instance Monad m => MonadReader r (RWST r w s m) where
    ask = RWST . UpdateT $ \(r, _) -> return (mempty, r)

instance (Monad m, Monoid w) => MonadWriter w (RWST r w s m) where
    tell x = RWST . UpdateT $ \_ -> return (inL (Trivial x), ())

instance Monad m => MonadState s (RWST r w s m) where
    get   = RWST . UpdateT $ \(_, s) -> return (mempty, s)
    put s = RWST . UpdateT $ \_ -> return (inR (Last (Just s)), ())

runRWST :: (Monad m, Monoid w) => RWST r w s m a -> r -> s -> m (w, s, a)
runRWST (RWST (UpdateT f)) r s = do
    (e, a) <- f (r, s)
    let (w, s') = untangle e
    return (getTrivial w, fromMaybe s (getLast s'), a)

main :: IO ()
main = do
    runReaderT (ask >>= liftIO . print) ("Hello" :: String)

    print =<< runWriterT (tell ("Hello" :: String) >> tell (" World" :: String))

    x <- flip runStateT ("Hello" :: String) $ do
        get >>= liftIO . print
        put ("Goodbye" :: String)
        get >>= liftIO . print
        put ("Goodbye again" :: String)
        get >>= liftIO . print
    print x

    y <- (\f -> runRWST f ("Env" :: String) ("Hello" :: String)) $ do
        ask >>= liftIO . print
        tell ("Hello" :: String) >> tell (" World" :: String)
        get >>= liftIO . print
        put ("Goodbye" :: String)
        get >>= liftIO . print
        put ("Goodbye again" :: String)
        get >>= liftIO . print
    print y
