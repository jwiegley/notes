{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ForeignFunctionInterface #-}

module Tuples where

import Foreign.C.Types

foreign import ccall
  call :: CInt -> CInt -> CInt -> CInt -> IO ()

data MyTuple = MyTuple {-# UNPACK #-} !CInt {-# UNPACK #-} !CInt

main :: IO ()
main = do
    let a = (# 10, 20 #) :: (# CInt, CInt #)
        b = MyTuple 30 40
    case a of
        (# x, y #) ->
            case b of
                MyTuple xx yy -> call x y xx yy
