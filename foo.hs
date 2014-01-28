{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

import Control.Applicative hiding (empty)
import Control.Exception (evaluate)
import Control.Monad (void)
import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8 (decimal, endOfLine, char)
import Data.ByteString as B (getContents)
import Data.ByteString.Char8 as S (readInt)
import Data.Maybe
import Data.Vector.Unboxed as V (fromList, length)

main :: IO ()
main = do
    contents <- B.getContents
    let Just l = maybeResult $ flip parse contents $ do
        numLines <- decimal <* endOfLine
        fmap V.fromList $ count numLines $
            (,) <$> (decimal :: Parser Int) <* char ' '
                <*> (maybe 0 fst . S.readInt
                         <$> takeWhile1 (/= 10) <* endOfLine)
    void $ evaluate (V.length l)
