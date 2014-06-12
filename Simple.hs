{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Please see the project README for more details:
--
--   https://github.com/jwiegley/simple-conduit/blob/master/README.md
--
--   Also see this blog article:
--
--   https://www.newartisans.com/2014/06/simpler-conduit-library

module Conduit.Simple where

import           Control.Applicative
import           Control.Concurrent.Async.Lifted
import           Control.Concurrent.STM
import           Control.Exception.Lifted
import           Control.Foldl
import           Control.Monad hiding (mapM)
import           Control.Monad.Base
import           Control.Monad.Catch hiding (bracket, catch)
import           Control.Monad.IO.Class
import           Control.Monad.Morph
import           Control.Monad.Primitive
import           Control.Monad.Trans.Control
import           Control.Monad.Trans.Either
import           Control.Monad.Trans.State
import           Data.Bifunctor
import           Data.Builder
import           Data.Function
import           Data.ByteString hiding (hPut, putStrLn)
import           Data.IOData
import           Data.IORef
import           Data.MonoTraversable
import           Data.Monoid
import           Data.NonNull as NonNull
import           Data.Sequences as Seq
import           Data.Sequences.Lazy
import qualified Data.Streaming.Filesystem as F
import           Data.Text
import           Data.Textual.Encoding
import           Data.Traversable
import           Data.Word
import           Prelude hiding (mapM)
import           System.FilePath ((</>))
import           System.IO
import           System.Random.MWC as MWC

-- | The Bool in this types means "continue processing".
newtype CollectT r m a = CollectT { runCollectT :: r -> m (Either r (r, a)) }

instance Monad m => Functor (CollectT a m) where
    fmap f (CollectT k) = CollectT $ \r -> fmap (fmap f) `liftM` k r
    {-# INLINE fmap #-}

instance Monad m => Applicative (CollectT a m) where
    pure x = CollectT $ \r -> return $ Right (r, x)
    {-# INLINE pure #-}
    CollectT f <*> CollectT x = CollectT $ \r -> do
        eres <- f r
        case eres of
            Left r' -> return $ Left r'
            Right (r', f') -> fmap (fmap f') `liftM` x r'
    {-# INLINE (<*>) #-}

instance Monad m => Monad (CollectT a m) where
    return = pure
    {-# INLINE return #-}
    CollectT m >>= f = CollectT $ \r -> do
        eres <- m r
        case eres of
            Left r' -> return $ Left r'
            Right (r', a) -> runCollectT (f a) r'
    {-# INLINE (>>=) #-}

-- | In the type variable below, r stands for "result", with much the same
--   meaning as you find in 'ContT'.  a is the type of each element in the
--   "stream".  The type of Source should recall 'foldM':
--
-- @
-- Monad m => (a -> b -> m a) -> a -> [b] -> m a
-- @
--
-- 'EitherT' is used to signal short-circuiting of the pipeline.
newtype Source m a = Source
    { getSource :: forall r. r -> (r -> a -> EitherT r m r) -> EitherT r m r }

type Conduit a m b = Source m a -> Source m b
type Sink a m r    = Source m a -> m r

-- type SourceC m a r   = ContT () (ContT () (StateT r m)) a

-- yieldMany' :: (Monad m, MonoFoldable mono) => mono -> SourceC m (Element mono) r
-- yieldMany' xs = ContT $ \yield -> ofoldlM (\() x -> yield x) () xs

-- sinkList' :: Monad m => SourceC m a ([a] -> [a]) -> m [a]
-- sinkList' await =
--     liftM ($ []) $ flip execStateT id $
--         flip runContT return $ callCC $ \_exit ->
--             runContT await $ \x -> lift get >>= \r -> do
--                 let y = r . (x:)
--                 -- exit y
--                 lift $ put y

type SourceC m a r = (a -> StateT r (EitherT r m) ()) -> StateT r (EitherT r m) ()

yieldMany' :: (Monad m, MonoFoldable mono) => mono -> SourceC m (Element mono) r
yieldMany' xs yield = ofoldlM (const yield) () xs

resolve' :: Monad m => r -> StateT r (EitherT r m) () -> m r
resolve' r m = either id id `liftM` runEitherT (execStateT m r)

sinkList' :: Monad m => SourceC m a ([a] -> [a]) -> m [a]
sinkList' await = liftM ($ []) $ resolve' id $ await $ \x -> modify (. (x:))

-- | When wrapped in a 'SourceWrapper' using 'wrap', Sources offer a number of
--   typeclass instances, one of which is Monad.  As a Monad, it behaves very
--   much list the list monad: the value bound is each element of the
--   iteration in turn.
--
-- @
-- sinkList $ getSource $ do
--     x <- wrap $ yieldMany [1..3]
--     y <- wrap $ yieldMany [4..6]
--     wrap $ yieldOne (x, y)
--
-- ==> [(1,4),(1,5),(1,6),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6)]
-- @
instance Monad m => Monoid (Source m a) where
    mempty = Source $ const . return
    mappend x y = Source $ \r f -> flip (getSource y) f =<< getSource x r f

instance Functor (Source m) where
    fmap f (Source await) = Source $ \z yield -> await z $ \r x -> yield r (f x)

instance Applicative (Source m) where
    pure x = Source $ \z yield -> yield z x
    Source f <*> Source g = Source $ \z yield ->
        f z $ \r x ->
            g r $ \r' y ->
                yield r' (x y)

instance Monad (Source m) where
    return = pure
    Source await >>= f = Source $ \z yield ->
        await z $ \r x ->
            getSource (f x) r $ \r' y ->
                yield r' y

newtype SinkWrapper a m r = SinkWrapper { getSink :: Source m a -> m r }

instance Monad m => Functor (SinkWrapper a m) where
    fmap f (SinkWrapper k) = SinkWrapper $ \await -> f `liftM` k await

-- | Promote any sink to a source.  This can be used as if it were a source
--   transformer (aka, a conduit):
--
-- >>> sinkList $ returnC $ sumC $ mapC (+1) $ sourceList [1..10]
-- [65]
returnC :: Monad m => m a -> Source m a
returnC f = Source $ \z yield -> yield z =<< lift f

-- | Compose a 'Source' and a 'Conduit' into a new 'Source'.  Note that this
--   is just flipped function application, so ($) can be used to achieve the
--   same thing.
infixl 1 $=
($=) :: a -> (a -> b) -> b
($=) = flip ($)
{-# INLINE ($=) #-}

-- | Compose a 'Conduit' and a 'Sink' into a new 'Sink'.  Note that this is
--   just function composition, so (.) can be used to achieve the same thing.
infixr 2 =$
(=$) :: (a -> b) -> (b -> c) -> a -> c
(=$) = flip (.)
{-# INLINE (=$) #-}

-- | Compose a 'Source' and a 'Sink' and compute the result.  Note that this
--   is just flipped function application, so ($) can be used to achieve the
--   same thing.
infixr 0 $$
($$) :: a -> (a -> b) -> b
($$) = flip ($)
{-# INLINE ($$) #-}

-- | This is just like 'Control.Monad.Trans.Either.bimapEitherT', but it only
--   requires a 'Monad' constraint rather than 'Functor'.
rewrap :: Monad m => (a -> b) -> EitherT a m a -> EitherT b m b
rewrap f k = EitherT $ bimap f f `liftM` runEitherT k
{-# INLINE rewrap #-}

rewrapM :: Monad m => (a -> EitherT b m b) -> EitherT a m a -> EitherT b m b
rewrapM f k = EitherT $ do
    eres <- runEitherT k
    runEitherT $ either f f eres
{-# INLINE rewrapM #-}

resolve :: Monad m => (r -> a -> EitherT r m r) -> r -> a -> m r
resolve await z f = either id id `liftM` runEitherT (await z f)
{-# INLINE resolve #-}

yieldMany :: (Monad m, MonoFoldable mono) => mono -> Source m (Element mono)
yieldMany xs = Source $ \z yield -> ofoldlM yield z xs
{-# INLINE yieldMany #-}

yieldOne :: Monad m => a -> Source m a
yieldOne x = Source $ \z yield -> yield z x
{-# INLINE yieldOne #-}

unfoldC :: Monad m => (b -> Maybe (a, b)) -> b -> Source m a
unfoldC f i = Source $ \z yield -> fix (\loop x r ->
        case f x of
            Nothing      -> return r
            Just (a, x') -> loop x' =<< yield r a) i z

enumFromToC :: (Monad m, Enum a, Eq a) => a -> a -> Source m a
enumFromToC start stop = Source $ \z yield -> fix (\loop a r ->
    if a == stop
    then return r
    else loop (succ a) =<< yield r a) start z

iterateC :: Monad m => (a -> a) -> a -> Source m a
iterateC f i = Source $ go i
  where
    go y z yield = loop y z
      where
        loop x r = let x' = f x
                   in loop x' =<< yield r x'

repeatC :: Monad m => a -> Source m a
repeatC x = Source go
  where
    go z yield = loop z
      where
        loop y = loop =<< yield y x
{-# INLINE repeatC #-}

replicateC :: Monad m => Int -> a -> Source m a
replicateC n x = Source $ go n
  where
    go i z yield = loop i z
      where
        loop n' r
            | n' >= 0   = loop (n' - 1) =<< yield r x
            | otherwise = return r

sourceLazy :: (Monad m, LazySequence lazy strict) => lazy -> Source m strict
sourceLazy = yieldMany . toChunks
{-# INLINE sourceLazy #-}

repeatMC :: Monad m => m a -> Source m a
repeatMC x = Source go
  where
    go z yield = loop z
      where
        loop r = loop =<< yield r =<< lift x

repeatWhileMC :: Monad m => m a -> (a -> Bool) -> Source m a
repeatWhileMC m f = Source go
  where
    go z yield = loop z
      where
        loop r = do
            x <- lift m
            if f x
                then loop =<< yield r x
                else return r

replicateMC :: Monad m => Int -> m a -> Source m a
replicateMC n m = Source $ go n
  where
    go i z yield = loop i z
      where
        loop n' r | n' > 0 = loop (n' - 1) =<< yield r =<< lift m
        loop _ r = return r

sourceHandle :: (MonadIO m, IOData a) => Handle -> Source m a
sourceHandle h = Source go
  where
    go z yield = loop z
      where
        loop y = do
            x <- liftIO $ hGetChunk h
            if onull x
                then return y
                else loop =<< yield y x

sourceFile :: (MonadBaseControl IO m, MonadIO m, IOData a)
           => FilePath -> Source m a
sourceFile path = Source $ \z yield ->
    bracket
        (liftIO $ openFile path ReadMode)
        (liftIO . hClose)
        (\h -> getSource (sourceHandle h) z yield)

sourceIOHandle :: (MonadBaseControl IO m, MonadIO m, IOData a)
               => IO Handle -> Source m a
sourceIOHandle f = Source $ \z yield ->
    bracket
        (liftIO f)
        (liftIO . hClose)
        (\h -> getSource (sourceHandle h) z yield)

stdinC :: (MonadBaseControl IO m, MonadIO m, IOData a) => Source m a
stdinC = sourceHandle stdin

initRepeat :: Monad m => m seed -> (seed -> m a) -> Source m a
initRepeat mseed f = Source $ \z yield ->
    lift mseed >>= \seed -> getSource (repeatMC (f seed)) z yield

initReplicate :: Monad m => m seed -> (seed -> m a) -> Int -> Source m a
initReplicate mseed f n = Source $ \z yield ->
    lift mseed >>= \seed -> getSource (replicateMC n (f seed)) z yield

sourceRandom :: (Variate a, MonadIO m) => Source m a
sourceRandom =
    initRepeat (liftIO MWC.createSystemRandom) (liftIO . MWC.uniform)

sourceRandomN :: (Variate a, MonadIO m) => Int -> Source m a
sourceRandomN =
    initReplicate (liftIO MWC.createSystemRandom) (liftIO . MWC.uniform)

sourceRandomGen :: (Variate a, MonadBase base m, PrimMonad base)
                => Gen (PrimState base) -> Source m a
sourceRandomGen gen = initRepeat (return gen) (liftBase . MWC.uniform)

sourceRandomNGen :: (Variate a, MonadBase base m, PrimMonad base)
                 => Gen (PrimState base) -> Int -> Source m a
sourceRandomNGen gen = initReplicate (return gen) (liftBase . MWC.uniform)

sourceDirectory :: (MonadBaseControl IO m, MonadIO m)
                => FilePath -> Source m FilePath
sourceDirectory dir = Source $ \z yield ->
    bracket
        (liftIO (F.openDirStream dir))
        (liftIO . F.closeDirStream)
        (go z yield)
  where
    go z yield ds = loop z
      where
        loop r = do
            mfp <- liftIO $ F.readDirStream ds
            case mfp of
                Nothing -> return r
                Just fp -> loop =<< yield r (dir </> fp)

sourceDirectoryDeep :: (MonadBaseControl IO m, MonadIO m)
                    => Bool -> FilePath -> Source m FilePath
sourceDirectoryDeep followSymlinks startDir = Source go
  where
    go z yield = start startDir z
      where
        start dir r = getSource (sourceDirectory dir) r entry
        entry r fp = do
            ft <- liftIO $ F.getFileType fp
            case ft of
                F.FTFile -> yield r fp
                F.FTFileSym -> yield r fp
                F.FTDirectory -> start fp r
                F.FTDirectorySym
                    | followSymlinks -> start fp r
                    | otherwise -> return r
                F.FTOther -> return r

dropC :: Monad m => Int -> Conduit a m a
dropC n (Source await) = Source $ \z yield ->
    rewrap snd $ await (n, z) (go yield)
  where
    go _ (n', r) _ | n' > 0 = return (n' - 1, r)
    go yield (_, r) x = rewrap (0,) $ yield r x

dropCE :: (Monad m, IsSequence seq)
       => Index seq -> Conduit seq m seq
dropCE n (Source await) = Source $ \z yield ->
    rewrap snd $ await (n, z) (go yield)
  where
    go yield (n', r) s
        | onull y   = return (n' - xn, r)
        | otherwise = rewrap (0,) $ yield r y
      where
        (x, y) = Seq.splitAt n' s
        xn = n' - fromIntegral (olength x)

dropWhileC :: Monad m => (a -> Bool) -> Conduit a m a
dropWhileC f (Source await) = Source $ \z yield ->
    rewrap snd $ await (f, z) (go yield)
  where
    go _ (k, r) x | k x = return (k, r)
    go yield (_, r) x = rewrap (const False,) $ yield r x

dropWhileCE :: (Monad m, IsSequence seq)
            => (Element seq -> Bool)
            -> Conduit seq m seq
dropWhileCE f (Source await) =
    Source $ \z yield -> rewrap snd $ await (f, z) (go yield)
  where
    go yield (k, r) s
        | onull x   = return (k, r)
        | otherwise = rewrap (const False,) $ yield r s
      where
        x = Seq.dropWhile k s

foldC :: (Monad m, Monoid a) => Sink a m a
foldC = foldMapC id

foldCE :: (Monad m, MonoFoldable mono, Monoid (Element mono))
       => Sink mono m (Element mono)
foldCE = foldlC (\acc mono -> acc <> ofoldMap id mono) mempty

foldlC :: Monad m => (a -> b -> a) -> a -> Sink b m a
foldlC f z (Source await) = resolve await z ((return .) . f)
{-# INLINE foldlC #-}

foldlCE :: (Monad m, MonoFoldable mono)
        => (a -> Element mono -> a) -> a -> Sink mono m a
foldlCE f = foldlC (ofoldl' f)

foldMapC :: (Monad m, Monoid b) => (a -> b) -> Sink a m b
foldMapC f = foldlC (\acc x -> acc <> f x) mempty

foldMapCE :: (Monad m, MonoFoldable mono, Monoid w)
          => (Element mono -> w) -> Sink mono m w
foldMapCE = foldMapC . ofoldMap

allC :: Monad m => (a -> Bool) -> Sink a m Bool
allC f = liftM getAll `liftM` foldMapC (All . f)

allCE :: (Monad m, MonoFoldable mono)
      => (Element mono -> Bool) -> Sink mono m Bool
allCE = allC . oall

anyC :: Monad m => (a -> Bool) -> Sink a m Bool
anyC f = liftM getAny `liftM` foldMapC (Any . f)

anyCE :: (Monad m, MonoFoldable mono)
      => (Element mono -> Bool) -> Sink mono m Bool
anyCE = anyC . oany

andC :: Monad m => Sink Bool m Bool
andC = allC id

andCE :: (Monad m, MonoFoldable mono, Element mono ~ Bool)
      => Sink mono m Bool
andCE = allCE id

orC :: Monad m => Sink Bool m Bool
orC = anyC id

orCE :: (Monad m, MonoFoldable mono, Element mono ~ Bool)
     => Sink mono m Bool
orCE = anyCE id

elemC :: (Monad m, Eq a) => a -> Sink a m Bool
elemC x = anyC (== x)

elemCE :: (Monad m, EqSequence seq) => Element seq -> Sink seq m Bool
elemCE = anyC . Seq.elem

notElemC :: (Monad m, Eq a) => a -> Sink a m Bool
notElemC x = allC (/= x)

notElemCE :: (Monad m, EqSequence seq) => Element seq -> Sink seq m Bool
notElemCE = allC . Seq.notElem

produceList :: Monad m => ([a] -> b) -> Source m a -> m b
produceList f (Source await) =
    (f . ($ [])) `liftM` resolve await id (\front x -> return (front . (x:)))
{-# INLINE produceList #-}

sinkLazy :: (Monad m, LazySequence lazy strict)
         => Sink strict m lazy
sinkLazy = produceList fromChunks
-- {-# INLINE sinkLazy #-}

sinkList :: Monad m => Sink a m [a]
sinkList = produceList id
{-# INLINE sinkList #-}

sinkVector :: (MonadBase base m, Vector v a, PrimMonad base)
           => Sink a m (v a)
sinkVector = undefined

sinkVectorN :: (MonadBase base m, Vector v a, PrimMonad base)
            => Int -> Sink a m (v a)
sinkVectorN = undefined

sinkBuilder :: (Monad m, Monoid builder, ToBuilder a builder)
            => Sink a m builder
sinkBuilder = foldMapC toBuilder

sinkLazyBuilder :: (Monad m, Monoid builder, ToBuilder a builder,
                    Builder builder lazy)
                => Sink a m lazy
sinkLazyBuilder = liftM builderToLazy . foldMapC toBuilder

sinkNull :: Monad m => Sink a m ()
sinkNull _ = return ()

awaitNonNull :: (Monad m, MonoFoldable a) => Conduit a m (Maybe (NonNull a))
awaitNonNull (Source await) = Source $ \z yield -> await z $ \r x ->
    maybe (return r) (yield r . Just) (NonNull.fromNullable x)

headCE :: (Monad m, IsSequence seq) => Sink seq m (Maybe (Element seq))
headCE = undefined

-- newtype Pipe a m b = Pipe { runPipe :: Sink a m b }

-- instance Monad m => Functor (Pipe a m) where
--     fmap f (Pipe p) = Pipe $ \await -> f `liftM` p await

-- instance Monad m => Monad (Pipe a m) where
--     return x = Pipe $ \_ -> return x
--     Pipe p >>= f = Pipe $ \await -> do
--         x <- p await
--         runPipe (f x) await

-- jww (2014-06-07): These two cannot be implemented without leftover support.
-- peekC :: Monad m => Sink a m (Maybe a)
-- peekC = undefined

-- peekCE :: (Monad m, MonoFoldable mono) => Sink mono m (Maybe (Element mono))
-- peekCE = undefined

lastC :: Monad m => Sink a m (Maybe a)
lastC (Source await) = resolve await Nothing (const (return . Just))

lastCE :: (Monad m, IsSequence seq) => Sink seq m (Maybe (Element seq))
lastCE = undefined

lengthC :: (Monad m, Num len) => Sink a m len
lengthC = foldlC (\x _ -> x + 1) 0

lengthCE :: (Monad m, Num len, MonoFoldable mono) => Sink mono m len
lengthCE = foldlC (\x y -> x + fromIntegral (olength y)) 0

lengthIfC :: (Monad m, Num len) => (a -> Bool) -> Sink a m len
lengthIfC f = foldlC (\cnt a -> if f a then cnt + 1 else cnt) 0

lengthIfCE :: (Monad m, Num len, MonoFoldable mono)
           => (Element mono -> Bool) -> Sink mono m len
lengthIfCE f = foldlCE (\cnt a -> if f a then cnt + 1 else cnt) 0

maximumC :: (Monad m, Ord a) => Sink a m (Maybe a)
maximumC (Source await) = resolve await Nothing $ \r y ->
    return $ Just $ case r of
        Just x -> max x y
        _      -> y

maximumCE :: (Monad m, OrdSequence seq) => Sink seq m (Maybe (Element seq))
maximumCE = undefined

minimumC :: (Monad m, Ord a) => Sink a m (Maybe a)
minimumC (Source await) = resolve await Nothing $ \r y ->
    return $ Just $ case r of
        Just x -> min x y
        _      -> y

minimumCE :: (Monad m, OrdSequence seq) => Sink seq m (Maybe (Element seq))
minimumCE = undefined

-- jww (2014-06-07): These two cannot be implemented without leftover support.
-- nullC :: Monad m => Sink a m Bool
-- nullC = undefined

-- nullCE :: (Monad m, MonoFoldable mono) => Sink mono m Bool
-- nullCE = undefined

sumC :: (Monad m, Num a) => Sink a m a
sumC = foldlC (+) 0

sumCE :: (Monad m, MonoFoldable mono, Num (Element mono))
      => Sink mono m (Element mono)
sumCE = undefined

productC :: (Monad m, Num a) => Sink a m a
productC = foldlC (*) 1

productCE :: (Monad m, MonoFoldable mono, Num (Element mono))
          => Sink mono m (Element mono)
productCE = undefined

findC :: Monad m => (a -> Bool) -> Sink a m (Maybe a)
findC f (Source await) = resolve await Nothing $ \r x ->
    if f x then left (Just x) else return r

mapM_C :: Monad m => (a -> m ()) -> Sink a m ()
mapM_C f (Source await) = resolve await () (const $ lift . f)
{-# INLINE mapM_C #-}

mapM_CE :: (Monad m, MonoFoldable mono)
        => (Element mono -> m ()) -> Sink mono m ()
mapM_CE = undefined

foldMC :: Monad m => (a -> b -> m a) -> a -> Sink b m a
foldMC f z (Source await) = resolve await z (\r x -> lift (f r x))

foldMCE :: (Monad m, MonoFoldable mono)
        => (a -> Element mono -> m a) -> a -> Sink mono m a
foldMCE = undefined

foldMapMC :: (Monad m, Monoid w) => (a -> m w) -> Sink a m w
foldMapMC f = foldMC (\acc x -> (acc <>) `liftM` f x) mempty

foldMapMCE :: (Monad m, MonoFoldable mono, Monoid w)
           => (Element mono -> m w) -> Sink mono m w
foldMapMCE = undefined

sinkFile :: (MonadBaseControl IO m, MonadIO m, IOData a)
         => FilePath -> Sink a m ()
sinkFile fp = sinkIOHandle (liftIO $ openFile fp WriteMode)

sinkHandle :: (MonadIO m, IOData a) => Handle -> Sink a m ()
sinkHandle = mapM_C . hPut

sinkIOHandle :: (MonadBaseControl IO m, MonadIO m, IOData a)
             => IO Handle -> Sink a m ()
sinkIOHandle alloc =
    bracket
        (liftIO alloc)
        (liftIO . hClose)
        . flip sinkHandle

printC :: (Show a, MonadIO m) => Sink a m ()
printC = mapM_C (liftIO . print)

stdoutC :: (MonadIO m, IOData a) => Sink a m ()
stdoutC = sinkHandle stdout

stderrC :: (MonadIO m, IOData a) => Sink a m ()
stderrC = sinkHandle stderr

mapC :: Monad m => (a -> b) -> Conduit a m b
mapC f (Source await) = Source $ \z yield -> await z $ \acc -> yield acc . f
{-# INLINE mapC #-}

mapC' :: Monad m => (a -> b) -> Conduit a m b
mapC' f (Source await) = Source $ \z yield -> await z $ \acc x ->
    let y = f x in y `seq` acc `seq` yield acc y
{-# INLINE mapC' #-}

mapCE :: (Monad m, Functor f) => (a -> b) -> Conduit (f a) m (f b)
mapCE = undefined

omapCE :: (Monad m, MonoFunctor mono)
       => (Element mono -> Element mono) -> Conduit mono m mono
omapCE = undefined

concatMapC :: (Monad m, MonoFoldable mono)
           => (a -> mono) -> Conduit a m (Element mono)
concatMapC f (Source await) = Source $ \z yield -> await z $ \r x -> ofoldlM yield r (f x)

concatMapCE :: (Monad m, MonoFoldable mono, Monoid w)
            => (Element mono -> w) -> Conduit mono m w
concatMapCE = undefined

takeC :: Monad m => Int -> Source m a -> Source m a
takeC n (Source await) = Source $ \z yield -> rewrap snd $ await (n, z) (go yield)
  where
    go yield (n', z') x
        | n' > 1    = next
        | n' > 0    = left =<< next
        | otherwise = left (0, z')
      where
        next = rewrap (n' - 1,) $ yield z' x

takeCE :: (Monad m, IsSequence seq) => Index seq -> Conduit seq m seq
takeCE = undefined

-- | This function reads one more element than it yields, which would be a
--   problem if Sinks were monadic, as they are in conduit or pipes.  There is
--   no such concept as "resuming where the last conduit left off" in this
--   library.
takeWhileC :: Monad m => (a -> Bool) -> Source m a -> Source m a
takeWhileC f (Source await) = Source $ \z yield -> rewrap snd $ await (f, z) (go yield)
  where
    go yield (k, z') x | k x = rewrap (k,) $ yield z' x
    go _ (_, z') _ = left (const False, z')

takeWhileCE :: (Monad m, IsSequence seq)
            => (Element seq -> Bool) -> Conduit seq m seq
takeWhileCE = undefined

takeExactlyC :: Monad m => Int -> Conduit a m b -> Conduit a m b
takeExactlyC = undefined

takeExactlyCE :: (Monad m, IsSequence a)
              => Index a -> Conduit a m b -> Conduit a m b
takeExactlyCE = undefined

concatC :: (Monad m, MonoFoldable mono) => Conduit mono m (Element mono)
concatC = undefined

filterC :: Monad m => (a -> Bool) -> Conduit a m a
filterC f (Source await) = Source $ \z yield ->
    await z $ \r x -> if f x then yield r x else return r

filterCE :: (IsSequence seq, Monad m)
         => (Element seq -> Bool) -> Conduit seq m seq
filterCE = undefined

mapWhileC :: Monad m => (a -> Maybe b) -> Conduit a m b
mapWhileC f (Source await) = Source $ \z yield -> await z $ \z' x ->
    maybe (left z') (yield z') (f x)

conduitVector :: (MonadBase base m, Vector v a, PrimMonad base)
              => Int -> Conduit a m (v a)
conduitVector = undefined

scanlC :: Monad m => (a -> b -> a) -> a -> Conduit b m a
scanlC = undefined

concatMapAccumC :: Monad m => (a -> accum -> (accum, [b])) -> accum -> Conduit a m b
concatMapAccumC = undefined

intersperseC :: Monad m => a -> Source m a -> Source m a
intersperseC s (Source await) = Source $ \z yield -> EitherT $ do
    eres <- runEitherT $ await (Nothing, z) $ \(my, r) x ->
        case my of
            Nothing ->
                return (Just x, r)
            Just y  -> do
                r' <- rewrap (Nothing,) $ yield r y
                rewrap (Just x,) $ yield (snd r') s
    case eres of
        Left (_, r)        -> return $ Left r
        Right (Nothing, r) -> return $ Right r
        Right (Just x, r)  -> runEitherT $ yield r x

encodeBase64C :: Monad m => Conduit ByteString m ByteString
encodeBase64C = undefined

decodeBase64C :: Monad m => Conduit ByteString m ByteString
decodeBase64C = undefined

encodeBase64URLC :: Monad m => Conduit ByteString m ByteString
encodeBase64URLC = undefined

decodeBase64URLC :: Monad m => Conduit ByteString m ByteString
decodeBase64URLC = undefined

encodeBase16C :: Monad m => Conduit ByteString m ByteString
encodeBase16C = undefined

decodeBase16C :: Monad m => Conduit ByteString m ByteString
decodeBase16C = undefined

mapMC :: Monad m => (a -> m b) -> Conduit a m b
mapMC f (Source await) = Source $ \z yield -> await z (\r x -> yield r =<< lift (f x))
{-# INLINE mapMC #-}

mapMCE :: (Monad m, Traversable f) => (a -> m b) -> Conduit (f a) m (f b)
mapMCE = undefined

omapMCE :: (Monad m, MonoTraversable mono)
        => (Element mono -> m (Element mono)) -> Conduit mono m mono
omapMCE = undefined

concatMapMC :: (Monad m, MonoFoldable mono)
            => (a -> m mono) -> Conduit a m (Element mono)
concatMapMC = undefined

filterMC :: Monad m => (a -> m Bool) -> Conduit a m a
filterMC f (Source await) = Source $ \z yield -> await z $ \z' x -> do
    res <- lift $ f x
    if res
        then yield z' x
        else return z'

filterMCE :: (Monad m, IsSequence seq)
          => (Element seq -> m Bool) -> Conduit seq m seq
filterMCE = undefined

iterMC :: Monad m => (a -> m ()) -> Conduit a m a
iterMC = undefined

scanlMC :: Monad m => (a -> b -> m a) -> a -> Conduit b m a
scanlMC = undefined

concatMapAccumMC :: Monad m
                 => (a -> accum -> m (accum, [b])) -> accum -> Conduit a m b
concatMapAccumMC = undefined

encodeUtf8C :: (Monad m, Utf8 text binary) => Conduit text m binary
encodeUtf8C = mapC encodeUtf8

decodeUtf8C :: MonadThrow m => Conduit ByteString m Text
decodeUtf8C = undefined

lineC :: (Monad m, IsSequence seq, Element seq ~ Char)
      => Conduit seq m o -> Conduit seq m o
lineC = undefined

lineAsciiC :: (Monad m, IsSequence seq, Element seq ~ Word8)
           => Conduit seq m o -> Conduit seq m o
lineAsciiC = undefined

unlinesC :: (Monad m, IsSequence seq, Element seq ~ Char)
         => Conduit seq m seq
unlinesC = concatMapC (:[Seq.singleton '\n'])

unlinesAsciiC :: (Monad m, IsSequence seq, Element seq ~ Word8)
              => Conduit seq m seq
unlinesAsciiC = concatMapC (:[Seq.singleton 10])

linesUnboundedC_ :: (Monad m, IsSequence seq, Eq (Element seq))
                 => Element seq -> Conduit seq m seq
linesUnboundedC_ sep (Source await) = Source $ \z yield -> EitherT $ do
    eres <- runEitherT $ await (z, n) (go yield)
    case eres of
        Left (r, _)  -> return $ Left r
        Right (r, t)
            | onull t   -> return $ Right r
            | otherwise -> runEitherT $ yield r t
  where
    n = Seq.fromList []

    go yield = loop
      where
        loop (r, t') t
            | onull y = return (r, t <> t')
            | otherwise = do
                r' <- rewrap (, n) $ yield r (t' <> x)
                loop r' (Seq.drop 1 y)
          where
            (x, y) = Seq.break (== sep) t

linesUnboundedC :: (Monad m, IsSequence seq, Element seq ~ Char)
                => Conduit seq m seq
linesUnboundedC = linesUnboundedC_ '\n'

linesUnboundedAsciiC :: (Monad m, IsSequence seq, Element seq ~ Word8)
                     => Conduit seq m seq
linesUnboundedAsciiC = linesUnboundedC_ 10

-- | The use of 'awaitForever' in this library is just a bit different from
--   conduit:
--
-- >>> awaitForever $ \x yield done -> if even x then yield x else done
awaitForever :: Monad m
             => (a -> (b -> EitherT r m r) -> EitherT r m r
                 -> EitherT r m r)
             -> Conduit a m b
awaitForever f (Source await) = Source $ \z yield ->
    await z $ \r x -> f x (yield r) (return r)

-- | Sequence a collection of sources.
--
-- >>> sinkList $ sequenceSources [yieldOne 1, yieldOne 2, yieldOne 3]
-- [[1,2,3]]
sequenceSources :: (Traversable f, Monad m) => f (Source m a) -> Source m (f a)
sequenceSources = sequenceA

-- | Zip sinks together.  This function may be used multiple times:
--
-- >>> let mySink s await => resolve await () $ \() x -> liftIO $ print $ s <> show x
-- >>> zipSinks sinkList (zipSinks (mySink "foo") (mySink "bar")) $ yieldMany [1,2,3]
-- "foo: 1"
-- "bar: 1"
-- "foo: 2"
-- "bar: 2"
-- "foo: 3"
-- "bar: 3"
-- ([1,2,3],((),()))
--
-- jww (2014-06-09): Can this be written sanely without resorting to IORefs?
zipSinks :: MonadIO m => Sink a m r -> Sink a m r'-> Sink a m (r, r')
zipSinks x y (Source await) = do
    res_s  <- liftIO $ newIORef (error "zipSinks: s never assigned a value")
    res_r' <- liftIO $ newIORef (error "zipSinks: r' never assigned a value")
    r <- x $ Source $ \rx yieldx -> do
        r' <- lift $ y $ Source $ \ry yieldy -> EitherT $ do
            (rx', ry') <- resolve await (rx, ry) $ \(rx', ry') u -> EitherT $ do
                eres <- runEitherT $ yieldx rx' u
                case eres of
                    Left r -> return $ Left (r, ry')
                    Right r -> do
                        eres' <- runEitherT $ yieldy ry' u
                        case eres' of
                            Left r' -> return $ Left (r, r')
                            Right r' -> return $ Right (r, r')
            liftIO $ writeIORef res_s rx'
            return $ Right ry'
        liftIO $ do
            writeIORef res_r' r'
            readIORef res_s
    r' <- liftIO $ readIORef res_r'
    return (r, r')

newtype ZipSink a m r = ZipSink { getZipSink :: Source m a -> m r }

instance Monad m => Functor (ZipSink a m) where
    fmap f (ZipSink k) = ZipSink $ liftM f . k

instance Monad m => Applicative (ZipSink a m) where
    pure x = ZipSink $ \_ -> return x
    ZipSink f <*> ZipSink x = ZipSink $ \await -> f await `ap` x await

-- | Send incoming values to all of the @Sink@ providing, and ultimately
--   coalesce together all return values.
--
-- Implemented on top of @ZipSink@, see that data type for more details.
sequenceSinks :: (Traversable f, Monad m)
              => f (Source m i -> m s) -> Source m i -> m (f s)
sequenceSinks = getZipSink . sequenceA . fmap ZipSink

-- zipConduitApp :: Monad m => Conduit a m (x -> y) r -> Conduit a m x r -> Conduit a m y r
-- zipConduitApp f arg = Source $ \z yield -> f z $ \r x -> arg r $ \_ y -> yield z (x y)

-- newtype ZipConduit a m r b = ZipConduit { getZipConduit :: Conduit a m b r }

-- instance Monad m => Functor (ZipConduit a m r) where
--     fmap f (ZipConduit p) = ZipConduit $ \z yield -> p z $ \r x -> yield r (f x)

-- instance Monad m => Applicative (ZipConduit a m r) where
--     pure x = ZipConduit $ yieldOne x
--     ZipConduit l <*> ZipConduit r = ZipConduit (zipConduitApp l r)

-- -- | Sequence a collection of sources.
-- --
-- -- >>> sinkList $ sequenceConduits [yieldOne 1, yieldOne 2, yieldOne 3]
-- -- [[1,2,3]]
-- sequenceConduits :: (Traversable f, Monad m)
--                 => f (Conduit a m b r) -> Conduit a m (f b) r
-- sequenceConduits = getZipConduit . sequenceA . fmap ZipConduit

asyncC :: (MonadBaseControl IO m, Monad m)
       => (a -> m b) -> Conduit a m (Async (StM m b))
asyncC f (Source await) = Source $ \k yield ->
    await k $ \r x -> yield r =<< lift (async (f x))

-- | Convert a 'Control.Foldl.FoldM' fold abstraction into a Sink.
--
--   NOTE: This requires ImpredicativeTypes in the code that uses it.
--
-- >>> fromFoldM (FoldM ((return .) . (+)) (return 0) return) $ yieldMany [1..10]
-- 55
fromFoldM :: Monad m => FoldM m a b -> Source m a -> m b
fromFoldM (FoldM step initial final) (Source await) =
    initial >>= flip (resolve await) ((lift .) . step) >>= final

-- | Convert a Sink into a 'Control.Foldl.FoldM', passing it into a
--   continuation.
--
-- >>> toFoldM sumC (\f -> Control.Foldl.foldM f [1..10])
-- 55
toFoldM :: Monad m
        => Sink a m r -> (forall r. FoldM (EitherT r m) a r -> EitherT r m r) -> m r
toFoldM sink f = sink $ Source $ \k yield -> f $ FoldM yield (return k) return

-- | A Source for exhausting a TChan, but blocks if it is initially empty.
sourceTChan :: TChan a -> Source STM a
sourceTChan chan = Source go
  where
    go z yield = loop z
      where
        loop r = do
            x  <- lift $ readTChan chan
            r' <- yield r x
            mt <- lift $ isEmptyTChan chan
            if mt
                then return r'
                else loop r'

sourceTQueue :: TQueue a -> Source STM a
sourceTQueue chan = Source go
  where
    go z yield = loop z
      where
        loop r = do
            x  <- lift $ readTQueue chan
            r' <- yield r x
            mt <- lift $ isEmptyTQueue chan
            if mt
                then return r'
                else loop r'

sourceTBQueue :: TBQueue a -> Source STM a
sourceTBQueue chan = Source go
  where
    go z yield = loop z
      where
        loop r = do
            x  <- lift $ readTBQueue chan
            r' <- yield r x
            mt <- lift $ isEmptyTBQueue chan
            if mt
                then return r'
                else loop r'

untilMC :: Monad m => m a -> m Bool -> Source m a
untilMC m f = Source go
  where
    go z yield = loop z
      where
        loop r = do
            x <- lift m
            r' <- yield r x
            cont <- lift f
            if cont
                then loop r'
                else return r'

whileMC :: Monad m => m Bool -> m a -> Source m a
whileMC f m = Source go
  where
    go z yield = loop z
      where
        loop r = do
            cont <- lift f
            if cont
                then lift m >>= yield r >>= loop
                else return r

-- jww (2014-06-08): These exception handling functions are useless, since we
-- can only catch downstream exceptions, not upstream as conduit users expect.

-- catchC :: (Exception e, MonadBaseControl IO m)
--        => Source m a -> (e -> Source m a) -> Source m a
-- catchC await handler z yield =
--     await z $ \r x -> catch (yield r x) $ \e -> handler e r yield

-- tryAroundC :: (Exception e, MonadBaseControl IO m)
--            => Source m a -> Source m a (Either e r)
-- tryAroundC _ (Left e) _ = return (Left e)
-- tryAroundC await (Right z) yield = rewrap Right go `catch` (return . Left)
--   where
--     go = await z (\r x -> rewrap (\(Right r') -> r') $ yield (Right r) x)

-- tryC :: (Exception e, MonadBaseControl IO m)
--      => Source m a -> Source m a (Either e a)
-- tryC (Source await) = Source $ \z yield -> await z $ \r x ->
--     catch (yield r (Right x)) $ \e -> yield r (Left (e :: SomeException))

-- tryC :: (MonadBaseControl IO m)
--        => Conduit a m b r -> Conduit a m (Either SomeException b) r
-- tryC f (Source await) = trySourceC (f await)
