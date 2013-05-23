module EpicMonic where

import Data.Char
import Data.Eq
import Data.Function
import Data.Int
import Data.List
import GHC.Integer
import Prelude ((+), fromIntegral) -- in honor of the Burning Bridges debate
import System.IO
import Text.Read

{- The goal in this module is to find evidence of the follow two functions
   in Haskell: One which is monic but not epic, and one which is epic but not
   monic.
-}

epicButNotMonic :: [a] -> Int
epicButNotMonic = length

monicButNotEpic :: Read a => [Char] -> a
monicButNotEpic = read

g1 :: [Char] -> Int
g1 = length . filter (== 'a')

h1 :: [Char] -> Integer
h1 = genericLength . filter (== 'a')

main = do
    -- If epicButNotMonic were monic, different inputs would yield different
    -- results.
    print $ epicButNotMonic . ((:[]) . g1) $ "alphabeta"
    print $ epicButNotMonic . ((:[]) . h1) $ "alphabetaa"

    -- epicButNotMonic is epic because for every input it yields a single
    -- value, allowing functions it is composed with to be distinguished by
    -- the result they yield from that value.  (Lots of Haskell functions are
    -- epic).
    print $ (+1) . epicButNotMonic $ ("alphabeta" :: [Char])
    print $ (+2) . epicButNotMonic $ ("alphabeta" :: [Char])

    -- If monicButNotEpic were epic, the same result from the same input would
    -- mean that the functions composed with are the same function.  However,
    -- they are clearly different, as the domains are finite and infinite,
    -- respectively.
    print $ ((+1) :: Int -> Int) . monicButNotEpic $ "123"
    print $ (fromIntegral . (+1) :: Integer -> Int) . monicButNotEpic $ "123"

    -- monicButNotEpic is monic because it preserves the uniqueness of output
    -- values from the functions it is composed with.
    print $ (monicButNotEpic :: [Char] -> Int) . sort $ "1423"
    print $ (monicButNotEpic :: [Char] -> Int) . reverse $ "1143"
