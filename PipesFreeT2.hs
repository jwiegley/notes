{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module PipesFreeT where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Data.Void
import System.IO
import qualified Pipes.Internal as Pipes

data Free f a = Pure a | Free (f (Free f a))

newtype BFree f a = BFree {
    runFree :: forall r. (a -> r) -> (f r -> r) -> r
}

toBFree :: Functor f => Free f a -> BFree f a
toBFree fr = BFree (go fr) where
  go (Pure a) p _ = p a
  go (Free x) p f = f (fmap (\y -> go y p f) x)

fromBFree :: Functor f => BFree f a -> Free f a
fromBFree (BFree k) = k Pure Free

-- This is the original type that we're breaking into its constituent parts.
-- The 'pipes' library fuses the three roles (Free, FreeT, ProxyF) for
-- efficiency's sake, since otherwise there is a great deal of wrapping and
-- unwrapping, not all of which can optimized away by newtypes (notably FreeF).
--
-- data Proxy a' a b' b m r
--     = Request a' (a  -> Proxy a' a b' b m r )
--     | Respond b  (b' -> Proxy a' a b' b m r )
--     | M          (m    (Proxy a' a b' b m r))
--     | PPure   r

-- The true core of 'pipes' is the fixed-point of a request/respond functor.
data ProxyF a' a b' b r = Request a' (a  -> r)
                        | Respond b  (b' -> r)
    deriving Functor

newtype FreeT f m a = FreeT
    { runFreeT :: forall r. (a -> m r) -> (f r -> m r) -> m r }

instance Functor (FreeT f m) where
    fmap f m = FreeT $ \k -> runFreeT m (k . f)

instance Applicative (FreeT f m) where
    pure  = return
    (<*>) = ap

instance Monad (FreeT f m) where
    return x = FreeT $ \k _ -> k x
    m >>= k  = FreeT $ \g c -> runFreeT m (\x -> runFreeT (k x) g c) c

instance MonadTrans (FreeT f) where
    lift m = FreeT $ \k _ -> m >>= k

-- instance (MonadIO m) => MonadIO (FreeT r m) where
--     liftIO = lift . liftIO

-- The Proxy type is a fusion of FreeT, Free and ProxyF.
newtype Proxy a' a b' b m r = Proxy { runProxy :: FreeT (ProxyF a' a b' b) m r }
  deriving (Functor, Applicative, Monad, MonadTrans)

-- Let's establish the basic functions of the isomorphism.
toPipesProxy :: Monad m => Proxy a' a b' b m r -> Pipes.Proxy a' a b' b m r
toPipesProxy = go . runProxy
  where
    go p = Pipes.M $ runFreeT p (return . Pipes.Pure) $ \case
        Request a' fa  -> return $ Pipes.Request a' fa
        Respond b  fb' -> return $ Pipes.Respond b  fb'

-- fromPipesProxy :: Monad m => Pipes.Proxy a' a b' b m r -> Proxy a' a b' b m r
-- fromPipesProxy = Proxy . go
--   where
--     go :: Pipes.Proxy a' a b' b m r -> FreeT (ProxyF a' a b' b) m r
--     go p = FreeT $ \k g -> case p of
--         Pipes.Request a' fa  ->
--             g $ Request a' ((\x -> runFreeT (go x) k g) . fa )
--         Pipes.Respond b  fb' ->
--             g $ Respond b  ((\x -> runFreeT (go x) k g) . fb')
--         Pipes.M m            ->
--             m >>= \x -> runFreeT (runProxy (fromPipesProxy x)) k g
--         Pipes.Pure r         -> k r

-- -- TODO: Equational reasoning proof of the isomorphism goes here:
-- --
-- -- id = toPipesProxy . fromPipesProxy
-- -- id = fromPipesProxy . toPipesProxy

-- runEffect :: Monad m => Proxy Void () () Void m r -> m r
-- runEffect = go . runProxy
--   where
--     go p = runFreeT p >>= \case
--         Free (Request _ f) -> go (f ())
--         Free (Respond _ f) -> go (f ())
--         Pure r             -> return r

-- respond :: Monad m => a -> Proxy x' x a' a m a'
-- respond a = Proxy $ FreeT $ return $ Free $ Respond a (FreeT . return . Pure)

-- type Producer  b     = Proxy Void () () b
-- type Producer' b m r = forall x' x. Proxy x' x () b m r

-- yield :: Monad m => a -> Producer' a m ()
-- yield = respond

-- stdinLn :: Producer String IO ()
-- stdinLn = do
--     eof <- lift isEOF        -- 'lift' an 'IO' action from the base monad
--     unless eof $ do
--         str <- lift getLine
--         yield str            -- 'yield' the 'String'
--         stdinLn              -- Loop

-- (//>) :: Monad m
--       => Proxy x' x b' b m a'
--       -> (b -> Proxy x' x c' c m b')
--       -> Proxy x' x c' c m a'
-- p0 //> fb = Proxy (go (runProxy p0))
--   where
--     go p = FreeT $ runFreeT p >>= \case
--         Free (Request x' fx)  -> return $ Free $ Request x' (go . fx)
--         Free (Respond b  fb') -> runFreeT $ runProxy (fb b) >>= go . fb'
--         Pure a                -> return $ Pure a

-- for :: Monad m
--     => Proxy x' x b' b m a'
--     -> (b -> Proxy x' x c' c m b')
--     -> Proxy x' x c' c m a'
-- for = (//>)

-- each :: Monad m => [a] -> Producer a m ()
-- each = mapM_ yield

-- main :: IO ()
-- main = do
--     runEffect $ for (each [1..4 :: Int]) (lift . print)
--     runEffect $ for stdinLn (lift . putStrLn)
