{-# LANGUAGE OverloadedStrings #-}

import Control.Applicative hiding (empty)
import Control.Exception (evaluate)
import Control.Monad (void)
import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8 (decimal, endOfLine, char)
import Data.ByteString as B (getContents)
import Data.ByteString.Char8 (readInt)
import Data.Strict.Tuple

main :: IO ()
main = do
    contents <- B.getContents
    let Just l = maybeResult $ flip parse contents $ do
        numLines <- decimal <* endOfLine
        count numLines $
            (:!:) <$> (decimal :: Parser Int) <* char ' '
                  <*> (maybe 0 Prelude.fst . readInt
                           <$> takeWhile1 (/= 10) <* endOfLine)
    void $ evaluate l
