{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}

module SpeedTest where

import Control.Applicative ((<$))
import Control.Concurrent.Async (async, pollSTM)
import Control.Concurrent.STM (atomically)
import Control.Exception (SomeException, throwIO)
import Control.Monad.Trans.Class (lift)
import Data.Conduit (($$), await)
import Foreign.Ptr (FunPtr)

type C'speed_test_cb = FunPtr (IO ())
foreign import ccall "wrapper" mk'speed_test_cb :: IO () -> IO C'speed_test_cb
foreign import ccall "speed_test" speed_test :: C'speed_test_cb -> IO ()

main :: IO ()
main = do
    let test = mk'speed_test_cb (return ()) >>= speed_test
    test
    w <- async test
    gather w $$ () <$ await
  where
    gather worker = do
        mres <- lift $ atomically $ pollSTM worker
#if SPEED_BUG
        lift $ putStrLn "..."
#endif
        case mres of
            Just (Left e)  -> lift $ throwIO (e :: SomeException)
            Just (Right r) -> return r
            Nothing        -> gather worker
