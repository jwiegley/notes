module Compose where

import Control.Applicative
import Control.Monad
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Distributive
import Data.Monoid
import Data.Tuple (swap)

class Codistributive f where
    codistribute :: Applicative g => f (g a) -> g (f a)

instance Codistributive Identity where
    codistribute (Identity x) = fmap Identity x

instance Codistributive Maybe where
    codistribute Nothing = pure Nothing
    codistribute (Just x) = fmap Just x

instance Codistributive (Either e) where
    codistribute (Left e) = pure (Left e)
    codistribute (Right x) = fmap Right x

instance Codistributive ((,) e) where
    codistribute (e, x) = fmap ((,) e) x

instance (Codistributive f, Functor f,
          Codistributive h) => Codistributive (Compose f h) where
    codistribute (Compose x) =
        fmap Compose (codistribute (fmap codistribute x))

-- instance (Monad f, Distributive f, Monad g, Functor g)
--          => Monad (Compose f g) where
--   return x = Compose $ return (return x)
--   Compose m >>= f =
--       let x = fmap (fmap (getCompose . f)) m in
--       let y = fmap distribute x in
--       Compose $ fmap join (join y)

instance (Monad f, Applicative f,
          Monad g, Functor g, Codistributive g) => Monad (Compose f g) where
  return x = Compose $ return (return x)
  Compose m >>= f = Compose $ do
      m' <- m
      let x = fmap (getCompose . f) m'
      m'' <- codistribute x
      return $ join m''

type ReaderT e = Compose ((->) e)

ask :: Monad m => ReaderT e m e
ask = Compose return

runReaderT :: ReaderT e m a -> e -> m a
runReaderT = getCompose

-- This only works when 'm' is Distributive.
type WriterT w (m :: * -> *) = Compose m ((,) w)

tell :: Monad m => w -> WriterT w m ()
tell w = Compose (return (w, ()))

runWriterT :: Monad m => WriterT w m a -> m (a, w)
runWriterT = liftM swap . getCompose

-- This would only work if 'm' is Distributive, and 's' is a Monoid so that
-- ((,) s) can be a Monad.
type StateT s m = Compose ((->) s) (Compose m ((,) s))

instance Monoid s => Monad ((,) s) where
    return x = (mempty, x)
    (s,x) >>= f = let (s',x') = f x in (s <> s', x')

get :: Monad m => StateT s m s
get = Compose $ \s -> Compose (return (s, s))

put :: Monad m => s -> StateT s m ()
put s = Compose $ \_ -> Compose (return (s, ()))

runStateT :: Monad m => StateT s m a -> s -> m (a, s)
runStateT (Compose m) s = liftM swap (getCompose (m s))

type IdentityT m = Compose m Identity

runIdentityT :: Monad m => IdentityT m a -> m a
runIdentityT = liftM runIdentity . getCompose

type MaybeT m = Compose m Maybe

runMaybeT :: MaybeT m a -> m (Maybe a)
runMaybeT = getCompose

type EitherT e m = Compose m (Either e)

runEitherT :: EitherT e m a -> m (Either e a)
runEitherT = getCompose

type ListT m = Compose m []

runListT :: ListT m a -> m [a]
runListT = getCompose

newtype Hom r m a = Hom { getHom :: a -> m r }

-- This can't work either, since `Hom r m` isn't even a Functor.
type ContT r m a = Compose (Hom r m) (Hom r m) a

runContT :: ContT r m a -> (a -> m r) -> m r
runContT (Compose m) = getHom m . Hom

callCC :: ((a -> ContT r m b) -> ContT r m a) -> ContT r m a
callCC f = Compose $ Hom $ \(Hom c) ->
    runContT (f (\x -> Compose $ Hom $ \_ -> c x)) c

test :: Identity String
test = do
    x1 <- flip runReaderT (10 :: Int) $ do
        x <- ask
        return (x + 20)
    unless (x1 == 30) $ error "x1"

    x2 <- runWriterT $ do
        tell ("Hello," :: String)
        tell " World!"
    unless (x2 == ((), "Hello, World!")) $ error "x2"

    x3 <- flip runStateT (Sum (10 :: Int)) $ do
        x <- get
        put (x + 10)
    unless (x3 == ((), Sum 20)) $ error "x3"

    x4 <- runIdentityT $
        return (20 :: Int)
    unless (x4 == 20) $ error "x4"

    x5 <- runMaybeT $
        return (20 :: Int)
    unless (x5 == Just 20) $ error "x5"

    x6 <- runEitherT $ do
        return (Left (30 :: Int))
        return (20 :: Int)
    unless (x6 == Left 30) $ error "x6"

    -- x7 <- runListT $ do
    --     x <- return [1 :: Int, 2]
    --     y <- return [4 :: Int, 5]
    --     return (x, y)
    -- unless (x7 == [(1,4), (1,5), (2,4), (2,5)]) $ error "x7"

    -- x8 <- flip runContT return $ do
    --     x <- callCC $ \k -> do
    --         k (15 :: Int)
    --     return x
    -- unless (x8 == 15) $ error "83"

    return "done"

main :: IO ()
main = print (runIdentity test)
