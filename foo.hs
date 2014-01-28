{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Exception (evaluate)
import Control.Monad
import Control.Applicative hiding (empty)
import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8 (decimal, endOfLine, char)
import Data.ByteString as B (getContents)
import Data.Vector as V (fromList, length)

main :: IO ()
main = do
    contents <- B.getContents
    let Just l = maybeResult $ flip parse contents $ do
        numLines <- decimal <* endOfLine
        fmap (V.fromList . map (\(!i, !s) -> (i, s))) $ count numLines $
            (,) <$> decimal <* char ' '
                <*> takeWhile1 (/= 10) <* endOfLine
    void $ evaluate (V.length l)
