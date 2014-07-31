module Main

data Identity a = Id a

runIdentity : Identity a -> a
runIdentity (Id a) = a

instance Functor Identity where
  map f (Id x) = Id (f x)

instance Applicative Identity where
  pure = Id
  (Id f) <$> (Id x) = Id (f x)

instance Monad Identity where
  (Id m) >>= f = f m

data Source : (m : Type -> Type) -> (a : Type) -> Type where
  Src : (r -> (r -> a -> m r) -> m r) -> Source m a

Conduit : Type -> (Type -> Type) -> Type -> Type
Conduit a m b = Source m a -> Source m b

Sink : Type -> (Type -> Type) -> Type -> Type
Sink a m r = Source m a -> m r

instance Functor (Source m) where
    map f (Src await) = Src $ \z, yield => await z (\r => yield r . f)

foldM : Monad m => (r -> a -> m r) -> r -> List a -> m r
foldM f z []        = return z
foldM f z (x :: xs) = f z x >>= flip (foldM f) xs

source : (r -> (r -> a -> m r) -> m r) -> Source m a
source = Src

sourceList : Monad m => List a -> Source m a
sourceList xs = source $ \z, yield => foldM yield z xs

mapC : Monad m => (a -> b) -> Conduit a m b
mapC = map

sink : Monad m => r -> (r -> a -> m r) -> Sink a m r
sink z f (Src await) = await z f

produceList : Monad m => (List a -> b) -> Sink a m b
produceList f =
    map (f . (\k => k [])) . sink id (\front, x => return (front . (x ::)))

sinkList : Monad m => Sink a m (List a)
sinkList = produceList id

main : IO ()
main = do
    print $ runIdentity $ sinkList $ mapC (+1) $ sourceList [1..10]
