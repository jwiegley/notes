{-# LANGUAGE OverloadedStrings #-}

module SinkHash where

import           Conduit.Simple
import           Control.Monad (liftM)
import           Control.Monad.IO.Class (MonadIO, liftIO)
import           Crypto.Hash
import qualified Data.ByteString as B

-- | A 'Sink' that hashes a stream of 'B.ByteString'@s@ and creates a digest
--   @d@.
sinkHash :: (Monad m, HashAlgorithm hash) => Sink B.ByteString m (Digest hash)
sinkHash = liftM hashFinalize . sink hashInit ((return .) . hashUpdate)

-- | Hashes the whole contents of the given file in constant memory.  This
--   function is just a convenient wrapper around 'sinkHash'.
hashFile :: (MonadIO m, HashAlgorithm hash) => FilePath -> m (Digest hash)
hashFile = liftIO . sinkHash . sourceFile
