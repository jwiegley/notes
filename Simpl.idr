module Simple

data Source : (m : Type -> Type) -> (a : Type) -> Type where
  Src : (r -> (a -> r -> m r) -> m r) -> Source m a

Conduit : Type -> (Type -> Type) -> Type -> Type
Conduit a m b = Source m a -> Source m b

Sink : Type -> (Type -> Type) -> Type -> Type
Sink a m r = Source m a -> m r

instance Functor (Source m) where
    map f (Src await) = Src $ \z, yield => await z (yield . f)

foldM : Monad m => (r -> a -> m r) -> r -> List a -> m r
foldM f z []        = return z
foldM f z (x :: xs) = f z x >>= flip (foldM f) xs

source : (r -> (r -> a -> m r) -> m r) -> Source m a
source await = Src $ \z, yield => await z (\r, x => yield x r)

sourceList : Monad m => List a -> Source m a
sourceList xs = source $ \z, yield => foldM yield z xs

map : Monad m => (a -> b) -> Conduit a m b
map = fmap

produceList : Monad m => (List a -> b) -> Sink a m b
produceList f =
    liftM (f . ($ [])) . sink id (\front, x => return (front . (x ::)))

sinkList : Monad m => Sink a m List a
sinkList = produceList id

main = do
    print $ runIdentity $ sinkList $ mapC (+1) $ sourceList [1..10]
