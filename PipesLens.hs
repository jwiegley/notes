{-# LANGUAGE RankNTypes #-}

module Pipes.Lens where

import           Control.Applicative
import qualified Control.Foldl as F
import           Control.Lens hiding (each)
import           Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import           Data.Foldable
import           Data.Monoid (Monoid(..), First)
import           Pipes
import           Pipes.Internal
import qualified Pipes.Prelude as P

-- 'toProxy' and 'fromProxy' are isomorphic
toProxy
    :: Monad m
    => (forall s.
           (a' -> (a  -> s) -> s)
        -> (b  -> (b' -> s) -> s)
        -> (m s -> s)
        -> (r -> s)
        -> s)
    -> Proxy a' a b' b m r
toProxy p = p Request Respond M Pure

fromProxy
    :: Monad m
    => Proxy a' a b' b m r
    -> (a' -> (a  -> s) -> s)
    -> (b  -> (b' -> s) -> s)
    -> (m s -> s)
    -> (r -> s)
    -> s
fromProxy p req res mon pur = go p
  where
    go p' = case p' of
        Request a' fa  -> req a' (go . fa)
        Respond b  fb' -> res b  (go . fb')
        M       m      -> mon (liftM go m)
        Pure    r      -> pur r

-- 'toProxyM' and 'fromProxyM' are functionally equivalent, but do not compose
-- to identity.
toProxyM
    :: Monad m
    => (forall s.
           (a' -> (a  -> m s) -> m s)
        -> (b  -> (b' -> m s) -> m s)
        -> (r -> m s)
        -> m s)
    -> Proxy a' a b' b m r
toProxyM p = M $ p
    (\a' fa  -> return $ Request a' (M . fa))
    (\b  fb' -> return $ Respond b  (M . fb'))
    (return . Pure)

fromProxyM
    :: Monad m
    => Proxy a' a b' b m r
    -> (a' -> (a  -> m s) -> m s)
    -> (b  -> (b' -> m s) -> m s)
    -> (r -> m s)
    -> m s
fromProxyM p req res pur = go p
  where
    go p' = case p' of
        Request a' fa  -> req a' (go . fa)
        Respond b  fb' -> res b  (go . fb')
        M       m      -> m >>= go
        Pure    r      -> pur r

foldOver :: Monad m => Fold s a -> s -> Producer a m ()
foldOver t x = each (x ^.. t)

foldBy :: Monad m => Fold s a -> Pipe s a m ()
foldBy t = await >>= \x -> each (x ^.. t)

narrow :: Monad m => Getting (First a) i a -> Pipe i a m ()
narrow l = for cat $ traverse_ yield . preview l

foldMap :: (Monoid b, Monad m) => (a -> b) -> Producer a m () -> m b
foldMap = F.purely P.fold . flip F.foldMap id

mapMaybe :: Monad m => (a -> Maybe b) -> Pipe a b m ()
mapMaybe f = for cat $ maybe (return ()) yield . f

mapM_ :: Monad m => (a -> m b) -> Consumer a m ()
mapM_ f = for cat $ void . lift . f

mconcat :: (Monoid a, Monad m) => Producer a m () -> m a
mconcat = F.purely P.fold F.mconcat

unfold :: Monad m => (b -> Maybe (a, b)) -> b -> Producer a m b
unfold f = loop
  where
    loop x = case f x of
        Nothing      -> return x
        Just (a, x') -> yield a >> loop x'

iterate :: Monad m => (a -> a) -> a -> Producer a m ()
iterate f = loop
  where
    loop x = yield x >> loop (f x)

repeat :: Monad m => a -> Producer a m ()
repeat = forever . yield

replicate :: Monad m => Int -> a -> Producer a m ()
replicate n = replicateM_ n . yield

chunksOfBs :: Traversal' BL.ByteString B.ByteString
chunksOfBs f bl = BL.fromChunks <$> traverse f (BL.toChunks bl)

-- Step through a computation that is equivalent to ContT () n a, turning it
-- into a producer.
collect :: Monad m => (forall n. (a -> n ()) -> n ()) -> Producer a m ()
collect loop = loop yield

examples :: IO ()
examples = do
    print "test 1.."
    runEffect $ each [Left 10, Right (20 :: Int), Left 30]
        >-> mapMaybe (preview _Left)
        >-> Pipes.Lens.mapM_ (print :: Int -> IO ())

    print "test 2.."
    runEffect $ each [(10, Left 'a'), (20, Right 'b'), (30, Left 'c')]
        >-> narrow (filtered (has (_2 . _Left . only 'a')) . _1)
        >-> Pipes.Lens.mapM_ (print :: Int -> IO ())
