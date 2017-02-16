{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}

module PipesFreeTAlt where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.Free.Church
import           Control.Monad.Trans.Class
import           Data.Void
import qualified Pipes.Internal as Pipes
import           System.IO

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
data ProxyF a' a b' b r
    = Request a' (a  -> r)
    | Respond b  (b' -> r)
    deriving Functor

-- The Proxy type is a fusion of FreeT (Church-encoded) and ProxyF.
newtype Proxy a' a b' b m r = Proxy { runProxy :: FT (ProxyF a' a b' b) m r }
    deriving (Functor, Applicative, Monad, MonadTrans)

-- Establish the isomorphism.
toPipesProxy :: forall a' a b' b m r. Monad m
             => Proxy a' a b' b m r -> Pipes.Proxy a' a b' b m r
toPipesProxy = go . runProxy
  where
    go m = Pipes.M $ runFT m (return . Pipes.Pure) $ \k -> \case
        Request a' fa  -> return $ Pipes.Request a' (Pipes.M . k . fa)
        Respond b  fb' -> return $ Pipes.Respond b  (Pipes.M . k . fb')

fromPipesProxy :: forall m a' a b' b r. Monad m
               => Pipes.Proxy a' a b' b m r -> Proxy a' a b' b m r
fromPipesProxy = Proxy . go
  where
    go p = FT $ \k g -> case p of
        Pipes.Request a' fa  -> g (\x -> runFT x k g) $ Request a' (go . fa )
        Pipes.Respond b  fb' -> g (\x -> runFT x k g) $ Respond b  (go . fb')
        Pipes.M m    -> m >>= \x -> runFT (runProxy (fromPipesProxy x)) k g
        Pipes.Pure r -> k r

-- TODO: Equational reasoning proof of the isomorphism goes here:
--
-- id = toPipesProxy . fromPipesProxy
-- id = fromPipesProxy . toPipesProxy

runEffect :: Monad m => Proxy Void () () Void m r -> m r
runEffect p = runFT (runProxy p) return $ \k -> \case
    Request _ f -> k (f ())
    Respond _ f -> k (f ())

respond :: Monad m => a -> Proxy x' x a' a m a'
respond a = Proxy $ FT $ \k g -> g id $ Respond a k

type Producer  b     = Proxy Void () () b
type Producer' b m r = forall x' x. Proxy x' x () b m r

yield :: Monad m => a -> Producer' a m ()
yield = respond

stdinLn :: Producer String IO ()
stdinLn = do
    eof <- lift isEOF        -- 'lift' an 'IO' action from the base monad
    unless eof $ do
        str <- lift getLine
        yield str            -- 'yield' the 'String'
        stdinLn              -- Loop

(//>) :: Monad m
      => Proxy x' x b' b m a'
      -> (b -> Proxy x' x c' c m b')
      -> Proxy x' x c' c m a'
p0 //> fb = Proxy (go (runProxy p0))
  where
    go p = FT $ \k g -> runFT p k $ \h -> \case
        Request x' fx  -> g h $ Request x' fx
        Respond b  fb' -> runFT (runProxy (fb b)) (h . fb') g

for :: Monad m
    => Proxy x' x b' b m a'
    -> (b -> Proxy x' x c' c m b')
    -> Proxy x' x c' c m a'
for = (//>)

each :: Monad m => [a] -> Producer a m ()
each = mapM_ yield

main :: IO ()
main = do
    runEffect $ for (each [1..4 :: Int]) (lift . print)
    runEffect $ for stdinLn (lift . putStrLn)
