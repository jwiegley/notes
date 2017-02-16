module Pico where

import Control.Exception
import Data.Ratio
import Data.Time
import Test.QuickCheck

toPicoSeconds :: UTCTime -> Integer
toPicoSeconds t = numerator x
  where
    x     = toRational day * 86400 * pico + psecs * pico
    day   = toModifiedJulianDay (utctDay t)
    psecs = toRational (utctDayTime t)
    pico  = 10^(12 :: Integer)

fromPicoSeconds :: Integer -> UTCTime
fromPicoSeconds x = UTCTime (ModifiedJulianDay dayPart) (fromRational psecs)
  where
    dayPart = x `div` day
    day     = 86400 * pico
    psecs   = (toRational x - toRational dayPart * day) / pico
    pico    = 10^(12 :: Integer)

prop_isoToPico :: UTCTime -> Bool
prop_isoToPico n = n == fromPicoSeconds (toPicoSeconds n)

prop_isoFromPico :: Integer -> Bool
prop_isoFromPico n = n == toPicoSeconds (fromPicoSeconds n)

main :: IO ()
main = do
    now <- getCurrentTime
    assert (prop_isoToPico now) $ quickCheck prop_isoFromPico
