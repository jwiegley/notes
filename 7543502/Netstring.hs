{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Conduit.Extra.Netstring where

import Control.Exception
import Control.Monad
import Control.Monad.Trans.Class
import Data.ByteString as B
import Data.ByteString.Char8 as BC
import Data.Char
import Data.Conduit
import Data.Conduit.Binary as CB
import Data.Conduit.List as CL
import Data.Typeable
import Data.Void

type Netstring = ByteString

-- ^ Convert a 'ByteString' to a Netstring-encoded 'ByteString'.
toNetstring :: ByteString -> Netstring
toNetstring bs = B.concat [BC.pack (show (B.length bs)), ":", bs, ","]

data NetstringException = NetstringMissingLengthDigits
                        | NetstringMissingColon
                        | NetstringIncorrectLength
                        | NetstringMissingComma
    deriving (Show, Typeable)

instance Exception NetstringException

-- ^ A conduit which allows streams an individual Netstring from a larger
--   ByteString stream.
recvNetstring :: MonadThrow m
              => Sink ByteString m a -> ConduitM ByteString Void m a
recvNetstring bsink = do
    len <- CB.takeWhile isDigit' =$ CL.consume
    when (Prelude.null len) $
        monadThrow NetstringMissingLengthDigits

    colon <- CB.head
    when (colon /= Just (fromIntegral (ord ':'))) $
        monadThrow NetstringMissingColon

    m   <- CB.take $ read (BC.unpack (B.concat len))
    res <- lift $ sourceLbs m $$ bsink

    comma <- CB.head
    when (comma /= Just (fromIntegral (ord ','))) $
        monadThrow NetstringMissingComma

    return res
  where
    isDigit' w = w >= 48 && w <= 57
