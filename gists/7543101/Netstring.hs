{-# LANGUAGE OverloadedStrings #-}

module Data.Conduit.Extra.Netstring where

import Control.Applicative
import Control.Monad
import Data.Attoparsec.ByteString.Char8
import Data.Attoparsec.ByteString as Atto (take)
import Data.ByteString as B
import Data.ByteString.Char8 as BC
import Data.Conduit
import Data.Conduit.List as CL

type Netstring = ByteString

-- ^ Convert a 'ByteString' to a Netstring-encoded 'ByteString'.
toNetstring :: ByteString -> Netstring
toNetstring bs = B.concat [BC.pack (show (B.length bs)), ":", bs, ","]

-- ^ Convert a Netstring-encoded 'ByteString' to 'ByteString', if it obeys the
-- proper formatting conventions.
fromNetstring :: Netstring -> Maybe ByteString
fromNetstring ns = maybeResult $ parse parseNS ns
  where
    parseNS = do
        l <- decimal <* char ':'
        Atto.take l <* char ','

-- ^ A conduit which encodes ByteStrings into Netstring-encoded ByteStrings.
encode :: Monad m => Conduit ByteString m Netstring
encode = CL.map toNetstring

-- ^ A conduit which decodes Netstring-encoded ByteStrings into ByteStrings,
--   stopping when either the end of input has been reached, or a ByteString
--   failed to decode (which is put back on the source as a leftover).
decode :: Monad m => Conduit Netstring m ByteString
decode = do
    mns <- await
    case mns of
        Nothing -> return ()
        Just ns -> case fromNetstring ns of
            Nothing -> void (leftover ns)
            Just bs -> yield bs >> decode
