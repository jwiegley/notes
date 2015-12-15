{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GADTs #-}

module Tuples where

import Foreign.C.Types
import Foreign.Storable
import Foreign.Ptr
import GHC.Prim

data MyTuple where
    MyTuple :: {-# UNPACK #-} Int -> {-# UNPACK #-} Int -> MyTuple

instance Storable MyTuple where
    sizeOf _ = 16
    peek addr = do
        x <- peek (castPtr addr :: Ptr Int)
        y <- peek (castPtr (addr `plusPtr` 8) :: Ptr Int)
        return $ MyTuple x y
    poke addr (MyTuple x y) = do
        poke (castPtr addr :: Ptr Int) x
        poke (castPtr (addr `plusPtr` 8) :: Ptr Int) y

foreign import ccall
  call :: MyTuple -> (# Int#, Int# #) -> IO ()

main :: IO ()
main = do
    let a = (# 10#, 20# #) :: (# Int#, Int# #)
        b = MyTuple 30 40
    call b a
