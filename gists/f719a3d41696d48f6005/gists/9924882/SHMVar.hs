{-# LANGUAGE OverloadedStrings #-}

module SHMVar where

import Control.Applicative
import Control.Exception
import Data.ByteString
import Data.Serialize
import System.Directory
import System.IO hiding (hGetContents)
import System.Posix.IO

data SHMVar a = SHMVar FilePath

withLock :: FilePath -> IOMode -> LockRequest -> (Handle -> IO a) -> IO a
withLock path mode req f = withBinaryFile path mode $ \h -> do
    fd <- handleToFd h
    (waitToSetLock fd (req, AbsoluteSeek, 0, 0) >> fdToHandle fd >>= f)
        `finally` waitToSetLock fd (Unlock, AbsoluteSeek, 0, 0)

newSHMVar :: Serialize a => a -> IO (SHMVar a)
newSHMVar x = do
    tmpDir <- getTemporaryDirectory
    (path, h) <- openTempFile tmpDir "shmvar."
    encodeWrite h x
        `finally` hClose h
        `onException` removeFile path
    return $ SHMVar path

deleteSHMVar :: SHMVar a -> IO ()
deleteSHMVar (SHMVar path) = removeFile path

encodeWrite :: Serialize a => Handle -> a -> IO ()
encodeWrite h x = hPut h (encode x)

writeSHMVar :: Serialize a => SHMVar a -> a -> IO ()
writeSHMVar (SHMVar path) x =
    withLock path WriteMode WriteLock $ \h -> encodeWrite h x

decodeRead :: Serialize b => Handle -> IO b
decodeRead h =
    either (error "Failed to decode SHMVar contents") id . decode
        <$> hGetContents h

readSHMVar :: Serialize a => SHMVar a -> IO a
readSHMVar (SHMVar path) = withLock path ReadMode ReadLock decodeRead

swapSHMVar :: Serialize a => SHMVar a -> a -> IO a
swapSHMVar (SHMVar path) x =
    withLock path ReadWriteMode WriteLock $ \h ->
        decodeRead h <* encodeWrite h x

main :: IO ()
main = do
    Prelude.putStrLn $ "main SHMVar.hs:56.."
    var <- newSHMVar (10 :: Int)
    Prelude.putStrLn $ "main SHMVar.hs:58.."
    x <- readSHMVar var
    Prelude.putStrLn $ "main SHMVar.hs:60.."
    print x
    Prelude.putStrLn $ "main SHMVar.hs:62.."
    deleteSHMVar var
