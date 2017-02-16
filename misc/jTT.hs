{-# LANGUAGE OverloadedStrings #-}

module JTT where

import Conduit
import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Data.ByteString
import Data.Char
import Data.Maybe
import Data.Monoid
import Data.Word8
import Filesystem.Path.CurrentOS

pC :: (MonadResource m, MonadIO m) => ConduitM Prelude.FilePath Int m ()
pC = loop
  where
    loop = do
      fp <- await
      case fp of
        Just f -> do
          x <- lift $ (sourceFile (decodeString f) :: MonadResource m => Producer m ByteString)
                    $$ foldlCE (\n (x :: Word8) ->
                                 if fromIntegral x == ord 'x' then n + 1 else n) 0
          yield x
          loop
        Nothing -> return ()

sink :: MonadIO m => ConduitM Int o m ()
sink = do
  fp <- await
  case fp of
   Just c -> do
     liftIO $ ( Prelude.putStrLn $ (show c))
     sink
   Nothing -> return ()

main :: IO ()
main = undefined
