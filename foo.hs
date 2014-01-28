-- Enter your code here. Read input from STDIN. Print output to STDOUT
{-# LANGUAGE BangPatterns, OverloadedStrings #-}

import Debug.Trace
import Control.Arrow
import Control.DeepSeq
import Control.Parallel.Strategies
import Control.Exception
import Control.Applicative hiding (empty)
import Control.Monad hiding (forM_)
import Control.Monad.ST
--import Data.Attoparsec.Text.Lazy (Parser, parse, maybeResult, decimal, count, takeWhile1, isEndOfLine, endOfLine, endOfInput)
import Data.Attoparsec.ByteString (takeWhile1, satisfy)
import Data.Attoparsec.ByteString.Lazy (Parser, parse, maybeResult)
import Data.Attoparsec.ByteString.Char8 (decimal, count, isEndOfLine, endOfLine, endOfInput, many1)
import Data.Foldable (toList, forM_)
import Data.ByteString (ByteString, putStr, pack)
import Data.ByteString.Char8 (unwords)
import Data.ByteString.Lazy (getContents)
--import Data.Text (Text, unwords)
--import Data.Text.IO (putStr)
--import Data.Text.Lazy.IO (getContents)
import Data.Traversable (mapAccumL, mapAccumR)
import Data.Vector (Vector, fromList, create, thaw, length, reverse, unzip)
import qualified Data.Vector as V
import Data.Vector.Mutable (MVector, new, replicate, read, write)
import Prelude hiding (getContents, putStr, unwords, replicate, read, length, reverse, unzip)

type Words = ByteString
data Pair a b = !a :!: !b deriving (Read, Show, Eq, Ord)

main = do
    contents <- getContents
    let Just !test = maybeResult $ parse inputParser contents
    _ <- evaluate $ (\(count :!: lines) -> solve count lines) test
    -- mapM putStr . toList $ (\(count :!: lines) -> solve count lines) test
    return ()

inputParser :: Parser (Pair Int (Vector (Pair Int Words)))
inputParser = do
    numLines <- decimal <* endOfLine
    !entries <- count numLines entryParser
    let !x = fromList entries
    return $ numLines :!: x

entryParser :: Parser (Pair Int Words)
entryParser = do
    num <- decimal <* " "
    str <- takeWhile1 (not . isEndOfLine) <* endOfLine
    return $ num :!: str

solve :: Int -> Vector (Pair Int Words) -> Vector Words
solve len !v = trace "solve" $ withStrategy rseq $ rearrange replaced aux where
    aux = cumSum . freqs $ v
    replaced = replace (len `div` 2) v

replace :: Int -> Vector (Pair Int Words) -> Vector (Pair Int Words)
replace num !v =
    let !res = snd . mapAccumR f num $ v
    in trace "replace" $ withStrategy rseq res
  where
	f !acc (i :!: s)
		| acc == 0 = let !x = (i :!: "-")
                             in (0, x)
		| otherwise = let !x = acc - 1
                                  !y = i :!: s
                              in (x, y)

rearrange :: Vector (Pair Int Words) -> Vector Int -> Vector Words
rearrange !es !is = trace "rearrange" $ withStrategy rseq $ create $ do
    sorted <- new $ trace ("length es = " ++ show (length es)) $ length es
    mis <- thaw is
    forM_ (reverse es) $ \(i :!: s) -> do
        index <- read mis i
        write sorted index $! s
        write mis i $! (index - 1)
    return $! sorted


freqs :: Vector (Pair Int Words) -> Vector Int
freqs !elems = trace "freqs" $ withStrategy rdeepseq $ create $ do
    freqCount <- replicate 100 0
    forM_ elems $ \(i :!: _) -> do
        count <- read freqCount i
        write freqCount i $! (count + 1)
    return freqCount

cumSum :: Vector Int -> Vector Int
cumSum = trace "cumSum" . snd . withStrategy rdeepseq . mapAccumL f (-1) where
    f acc e = let !x = acc + e in (x, x)
