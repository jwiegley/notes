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

data Dynamic t a = Dynamic (Behavior (Unique, a)) (Event (Unique, a))

instance Functor (Dynamic t) where
    fmap f (Dynamic (Behavior br) (Event er)) = unsafePerformIO $ do
        (bu, b) <- readIORef br
        me <- readIORef er
        case me of
            Nothing -> do
                b'u <- newUnique
                b' <- newIORef (b'u, f b)
                e' <- newIORef Nothing
                return $ Dynamic (Behavior b') (Event e')
            Just (eu, e)
                | bu == eu -> do
                    let x = f e
                    e'u <- newUnique
                    b' <- newIORef (e'u, x)
                    e' <- newIORef (Just (e'u, x))
                    return $ Dynamic (Behavior b') (Event e')
                | otherwise -> do
                    b'u <- newUnique
                    b' <- newIORef (b'u, f b)
                    e'u <- newUnique
                    e' <- newIORef (Just (e'u, f e))
                    return $ Dynamic (Behavior b') (Event e')
