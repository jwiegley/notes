{-# LANGUAGE OverloadedStrings #-}

import Control.Exception (evaluate)
import Control.Applicative hiding (empty)
import Data.Attoparsec.ByteString.Lazy
import Data.Attoparsec.ByteString.Char8 (decimal, endOfLine, char)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy as BL (getContents)
import Data.Vector as V (Vector, fromList, length)

main :: IO ()
main = do
    contents <- BL.getContents
    let Just l = maybeResult $ parse inputParser contents
    _ <- evaluate (V.length l)
    return ()

inputParser :: Parser (Vector (Int, ByteString))
inputParser = do
    numLines <- decimal <* endOfLine
    fromList <$> count numLines entryParser

entryParser :: Parser (Int, ByteString)
entryParser = (,) <$> decimal <* char ' '
                  <*> takeWhile1 (/= 10) <* endOfLine
