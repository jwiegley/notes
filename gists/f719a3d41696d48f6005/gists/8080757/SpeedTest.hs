{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}

module SpeedTest where

import Control.Concurrent.Async (withAsync, poll)
import Control.Exception (SomeException, throwIO)
import Foreign.Ptr (FunPtr)

type C'speed_test_cb = FunPtr (IO ())
foreign import ccall "wrapper" mk'speed_test_cb :: IO () -> IO C'speed_test_cb
foreign import ccall "speed_test" speed_test :: C'speed_test_cb -> IO ()

main :: IO ()
main = do
    let test = mk'speed_test_cb (return ()) >>= speed_test
    test
    withAsync test gather
  where
    gather worker = do
        mres <- poll worker
#if SPEED_BUG
        putStrLn "..."
#endif
        case mres of
            Just (Left e)  -> throwIO (e :: SomeException)
            Just (Right r) -> return r
            Nothing        -> gather worker
