{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Distributive
import Data.Functor.Rep
import Data.IORef
import System.IO.Unsafe
import System.Mem.Weak
import Unsafe.Coerce
import Data.Unique

data Behavior a = Behavior (IORef a)
data Event a = Event (IORef (Maybe a))

data Dynamic t a = forall f. (Functor f, Representable f)
    => Dynamic (Behavior (Unique, a)) (Event (Unique, a)) (f a)

instance Functor (Dynamic t) where
    fmap f (Dynamic k xs h) = Dynamic k xs (fmap f h)

data IORefRef a where
    IORefRef :: Weak (IORef a) -> IORefRef a

instance Functor IORefRef where
    fmap f (IORefRef w) = unsafePerformIO $ do
        ref <- deRefWeak w
        modifyIORef ref f
        return $ IORefRef ref

instance Distributive IORefRef where
    distribute _ = unsafeCoerce IORefRef

instance Representable IORefRef where
    type Rep IORefRef = ()
    tabulate _ = unsafeCoerce IORefRef
    index IORefRef ref = unsafePerformIO $ readIORef ref

main :: IO ()
main = do
    cell <- newIORef (10 :: Int)
    b' <- newIORef cell
    let b = Behavior b'
    e' <- newIORef Nothing
    let e = Event e'
    let d = Dynamic b e IORefRef
    let d' = fmap (+2) d
    case d' of
        Dynamic (Behavior ref) _ x -> do
            r <- readIORef ref
            let y = index x r
            print y
