{-
A brain-dead effectful streaming library, just to see how much we can get away
with, using as little as possible.  I.e., the one-legged centipede version of
conduit. :-)

Features conspicuously lacking:

    - Conduits are not Monads, which omits a lot of important use cases
    - No leftovers

Features surprisingly present:

    - Performance within 20% of conduit in simple cases
    - Early termination by consumers
    - Notification of uptream termination
    - Not a continuation, so monad-control can be used for resource control
    - Prompt finalization
    - Sources are Monoids (though making it an instance takes more work)

What's interesting is that this library is simply a convenience for chaining
monadic folds, and nothing more.  I find it interesting how much of conduit
can be expressed using only that abstraction.
-}

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}

module Contuit where

import qualified Conduit as C
import           Control.Exception.Lifted
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Control
import           Criterion.Main (defaultMain, bench, nf)
import           Data.Functor.Identity
import           Data.IOData
import           Data.MonoTraversable
import           Data.Sequences.Lazy
import           Data.Text as T
import           Data.Text.Encoding
import           System.IO

type Source m a    = forall r. r -> (a -> r -> m (Maybe r)) -> m r
type Conduit a m b = Source m a -> Source m b
type Sink a m r    = Source m a -> m r

infixl 1 $=
($=) :: Monad m => Source m a -> Conduit a m b -> Source m b
l $= r = r l
{-# INLINE ($=) #-}

infixr 2 =$
(=$) :: Monad m => Conduit a m b -> Sink b m r -> Sink a m r
l =$ r = \await -> r (l await)
{-# INLINE (=$) #-}

infixr 0 $$
($$) :: Monad m => Source m a -> Sink a m r -> m r
($$) = flip ($)
{-# INLINE ($$) #-}

-- | Since Source is not a Monad in this library, they can be sequentially
--   "chained" using this append operator.  If Source were a newtype, we could
--   make it an instance of Monoid.
(<+>) :: Monad m => Source m a -> Source m a -> Source m a
x <+> y = \r f -> flip y f =<< x r f
{-# INLINE (<+>) #-}

sourceList :: Monad m => [a] -> Source m a
sourceList xs z yield = go z xs
  where
    go z' []     = return z'
    go z' (y:ys) = maybe (return z') (`go` ys) =<< yield y z'
{-# INLINE sourceList #-}

unfoldC :: Monad m => (b -> Maybe (a, b)) -> b -> Source m a
unfoldC f i z yield = go i z
  where
    go x y = case f x of
        Nothing      -> return y
        Just (a, x') -> maybe (return y) (go x') =<< yield a y

iterateC :: Monad m => (a -> a) -> a -> Source m a
iterateC f i z yield = go i z
  where
    go x y = let x' = f x
             in maybe (return y) (go x') =<< yield x' y

repeatC :: Monad m => a -> Source m a
repeatC x z yield = go z
  where
    go y = maybe (return y) go =<< yield x y
{-# INLINE repeatC #-}

replicateC :: Monad m => Int -> a -> Source m a
replicateC n x z yield = go n z
  where
    go n' y
        | n' >= 0   = maybe (return y) (go (n' - 1)) =<< yield x y
        | otherwise = return y

sourceLazy :: (Monad m, LazySequence lazy strict) => lazy -> Source m strict
sourceLazy l = sourceList (toChunks l)
{-# INLINE sourceLazy #-}

sourceFile :: (MonadBaseControl IO m, MonadIO m, IOData a)
           => FilePath -> Source m a
sourceFile path z yield =
    bracket
        (liftIO $ openFile path ReadMode)
        (liftIO . hClose)
        (`go` z)
  where
    go h y = do
        x <- liftIO $ hGetChunk h
        if onull x
            then return y
            else do
                mz <- yield x y
                case mz of
                    Nothing -> return y
                    Just z' -> go h z'

mapC :: Monad m => (a -> b) -> Conduit a m b
mapC f await z yield = await z (yield . f)
{-# INLINE mapC #-}

mapMC :: Monad m => (a -> m b) -> Conduit a m b
mapMC f await z yield = await z (\x r -> flip yield r =<< f x)
{-# INLINE mapMC #-}

mapM_C :: Monad m => (a -> m ()) -> Sink a m ()
mapM_C f await = await () (\a () -> Just `liftM` f a)
{-# INLINE mapM_C #-}

dropC :: Monad m => Int -> Conduit a m a
dropC n await z yield = liftM snd $ await (n, z) go
  where
    go x (n', z')
        | n' > 0    = return $ Just (n' - 1, z')
        | otherwise = fmap (n' - 1,) `liftM` yield x z'

takeC :: Monad m => Int -> Conduit a m a
takeC n await z yield = liftM snd $ await (n, z) go
  where
    go x (n', z')
        | n' > 0    = fmap (n' - 1,) `liftM` yield x z'
        | otherwise = return Nothing

sinkList :: Monad m => Sink a m [a]
sinkList await =
    ($ []) `liftM` await id (\x front -> return (Just (front . (x:))))
{-# INLINE sinkList #-}

main :: IO ()
main = do
    xs <- sourceList [1..10] $= mapC (+2) $$ sinkList
    print (xs :: [Int])

    ys <- sourceList [1..10] $$ mapC (+2) =$ sinkList
    print (ys :: [Int])

    zs <- sourceList [1..10] $= dropC 5 $= mapC (+2) $$ sinkList
    print (zs :: [Int])

    ws <- sourceList [1..10] $= takeC 5 $= mapC (+2) $$ sinkList
    print (ws :: [Int])

    us <- sourceFile "Contuit.hs" $= takeC 1 $$ sinkList
    print (T.unpack (decodeUtf8 (Prelude.head us)))

    sourceList ([1..10] :: [Int]) $$ mapM_C (liftIO . print)

    defaultMain [
        bench "centipede" $ nf (runIdentity . useThis) ([1..1000000] :: [Int])
      , bench "conduit"   $ nf (runIdentity . useThat) ([1..1000000] :: [Int])
      ]
  where
    useThis xs = sourceList xs $= mapC (+2) $$ sinkList
    useThat xs = C.yieldMany xs C.$= C.mapC (+2) C.$$ C.sinkList
