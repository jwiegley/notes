{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Trans.Reader
import qualified Data.Attoparsec.ByteString as Atto
import qualified Data.ByteString.Char8 as B
import           Data.List
import           Data.Maybe
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Time.Calendar
import           Data.Time.Calendar.WeekDate
import           Data.Time.Clock
import           Data.Time.Format
import           Data.Time.LocalTime
import qualified Data.Time.Parsers as Time
import           Data.Time.Recurrence as R
import           Options.Applicative
import           Options.Applicative.Types (ReadM(..))
import           Prelude hiding (filter)
import           Shelly
import           System.IO.Unsafe
import           System.Locale
import           Text.Printf

myTimeZone :: TimeZone
myTimeZone = TimeZone (-300) True "CDT"

baeTimeZone :: TimeZone
baeTimeZone = TimeZone (-240) True "EDT"

{-@ mkUTCTime :: { y : Integer | y >= 1970 && y < 2100 }
              -> { m : Int | m >= 1 && m <= 12 }
              -> { d : Int | d >= 1 && d <= 31 }
              -> { h : Int | h >= 0 && h < 24 }
              -> { mi : Int | mi >= 0 && mi < 60 }
              -> { s : Int | s >= 0 && s < 60 }
              -> UTCTime
@-}
mkUTCTime :: Integer -> Int -> Int -> Int -> Int -> Int -> UTCTime
mkUTCTime year month day hour minute second =
    localTimeToUTC baeTimeZone $ LocalTime
        (fromGregorian (fromIntegral year) (fromIntegral month)
                       (fromIntegral day))
        (TimeOfDay (fromIntegral hour) (fromIntegral minute)
                   (realToFrac second))

{-@
measure fstof3 :: (a, b, c) -> a
fstof3 (x, _, _) = x

measure sndof3 :: (a, b, c) -> b
sndof3 (_, x, _) = x

measure thrdof3 :: (a, b, c) -> c
thrdof3 (_, _, x) = x
@-}

{-@ toGregorian
        :: Day
        -> { ymd : (Integer, Int, Int)
          | fstof3 ymd >= 1970 && fstof3 ymd < 2100 &&
            sndof3 >= 1 && sndof3 <= 12
            thrdof3 >= 1 && thrdof3 <= 31 }
@-}

{-@ mostRecentFridayNoon
        :: { y : Integer | y >= 1970 && y < 2100 }
        -> { m : Int | m >= 1 && m <= 12 }
        -> { d : Int | d >= 1 && d <= 31 }
        -> { h : Int | h >= 0 && h < 24 }
        -> { adj : Integer | adj >= 0 }
        -> UTCTime
@-}
mostRecentFridayNoon :: Integer -> Int -> Int -> Int -> Integer -> UTCTime
mostRecentFridayNoon year month day hour adjust =
    let d = adjust `addDays`
            fromGregorian (fromIntegral year) (fromIntegral month)
                          (fromIntegral day)
        (_,_,dow) = toWeekDate d
        diff = toInteger (dow - 5)
        d' = ModifiedJulianDay $ toModifiedJulianDay d
             - (if diff < 0
                then 7 + diff
                else diff)
             - (if diff == 0 && hour < 12
                then 7
                else 0)
        (year', month', day') = toGregorian d'
    in mkUTCTime year' month' day' 12 0 0

baeWeekRange :: Integer -> Int -> Int -> Int -> (UTCTime,UTCTime)
baeWeekRange year month day hour =
    let f = mostRecentFridayNoon year month day hour in (f 0, f 7)

holidays :: Integer -> Int -> [Int]
holidays year month =
    fromMaybe [] $ join $ lookup month <$> lookup year
        [ (2014, [ (12, [25, 26]) ])
        , (2015, [ ( 1, [1])
                 ])
        ]

baeWorkHoursForDay :: Integer -> Int -> Int -> Int
baeWorkHoursForDay year month day =
    case fromGregorianValid year month day of
        Nothing -> error $ "workHoursForDay: invalid date: "
                       ++ show (year, month, day)
        Just (toWeekDate -> (_,_,dow))
            | day `elem` holidays year month -> 0
            | dow == 5  -> 4     -- Friday
            | otherwise -> 9

countWorkHours :: UTCTime -> UTCTime -> Int
countWorkHours beg end =
    sum $ map (uncurry3 baeWorkHoursForDay . toGregorian . utctDay)
        $ takeWhile (< end)
        $ starting beg
        $ recur daily >==> R.filter (WeekDays [Monday .. Friday])
  where
    uncurry3 f (a,b,c) = f a b c

isWeekendDay :: Day -> Bool
isWeekendDay day = let (_,_,dow) = toWeekDate day in dow == 6 || dow == 7

balanceTotal :: Text -> Text -> Sh Float
balanceTotal journal period = do
    setStdin journal
    balance <- run "ledger" ["-f", "-", "--base", "-F", "%(scrub(total))\n"
                           , "-p", period, "--day-break", "bal"]
    return $ case T.lines balance of
        [] -> 0.0 :: Float
        xs -> (/ 3600.0)
           $ (read :: String -> Float) . T.unpack . T.init
           $ T.dropWhile (== ' ') (last xs)

data Options = Options
    { verbose  :: Bool
    , file     :: String
    , period   :: String
    , category :: String
    , archive  :: String
    , moment   :: LocalTime
    }

options :: Parser Options
options = Options
    <$> switch (long "verbose" <> help "Display statistics")
    <*> strOption (long "file" <> help "Active timelog file to use")
    <*> strOption (long "period" <> help "Period to report for" <> value "")

    <*> strOption (long "category"
                   <> help "Account/category to query from timelog"
                   <> value "")

    <*> strOption (long "archive" <> help "Archival timelog" <> value "")

    <*> option
          (ReadM $ asks $ fromJust . Atto.maybeResult .
               Time.parseWithDefaultOptions Time.defaultLocalTime . B.pack)
          (long "moment" <> help "Set notion of the current moment"
           <> value (unsafePerformIO $
                     (zonedTimeToLocalTime <$>) getZonedTime))

main :: IO ()
main = execParser opts >>= doMain
  where
    opts = info (helper <*> options)
                (fullDesc
                 <> progDesc "Show hours worked so far"
                 <> header "hours - show hours worked so far")

doMain :: Options -> IO ()
doMain opts = shelly $ silently $ do
    let per = if null (period opts)
               then Nothing
               else Just (T.pack (period opts))

    now <- if isNothing per
          then return (moment opts)
          else do
              dateString <-
                  run "ledger" [ "eval", "--now", fromJust per, "today" ]
              return . fromJust $
                  parseTime defaultTimeLocale "%Y/%m/%d" (T.unpack dateString)

    let today     = toGregorian (localDay now)
        yr        = fromIntegral (today^._1)
        mon       = fromIntegral (today^._2)
        day       = fromIntegral (today^._3)
        mnight    = localTimeToUTC baeTimeZone
                        (LocalTime (localDay now) midnight)
        thishr    = todHour (localTimeOfDay now)
        (beg,end) = baeWeekRange yr mon day thishr
        tdyBeg    = if today == toGregorian (utctDay beg)
                    then beg
                    else mnight
        thismom   = diffUTCTime (localTimeToUTC myTimeZone now) tdyBeg
        fmtTime   = T.pack . formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S"
                           . utcToLocalTime myTimeZone
        begs      = fmtTime beg
        ends      = fmtTime end
        fmtDate   = T.pack . formatTime defaultTimeLocale "%Y-%m-%d"
                           . utcToLocalTime myTimeZone

    activeTimelog <- run "org2tc" [T.pack (file opts), begs, ends]
    let (is, os) = partition (== 'i') $ map T.head (T.lines activeTimelog)
        loggedIn = length is > length os

    setStdin activeTimelog
    data1 <- run "ledger" (["-f", "-", "--day-break", "print"])
    data2 <- if null (archive opts)
            then return ""
            else run "org2tc" [T.pack (archive opts), begs, ends]
                     -|- run "ledger" ["-f", "-", "--day-break", "print"]

    let combined = T.concat [data1, "\n", data2]

    realHrs  <- balanceTotal combined (fromMaybe ("since " <> fmtDate beg) per)
    todayHrs <- balanceTotal combined "today"

    let currHour  = fromIntegral (ceiling thismom) / 3600.0 / 3.0
        workHrs   = countWorkHours beg end
        targHrs   = countWorkHours beg mnight
        isWeekend = isWeekendDay (localDay now)
        targetHrs = if isNothing per
                    then (if isWeekend then 0 else currHour) +
                         fromIntegral targHrs
                    else fromIntegral workHrs
        discrep   = realHrs - targetHrs
        hoursLeft = fromIntegral workHrs - realHrs
        indicator = if discrep < 0
                    then "\ESC[31m↓\ESC[0m"
                    else "\ESC[32m↑\ESC[0m"
        paceMark  = (realHrs * 100.0) / fromIntegral workHrs

    when (verbose opts) $ liftIO $
        putStrLn $ unlines
            [ "today:       " ++ show today
            , "now:         " ++ show now
            , "beg:         " ++ T.unpack begs
            , "end:         " ++ T.unpack ends
            , "midnight:    " ++ T.unpack (fmtTime mnight)
            , "tdyBeg:      " ++ T.unpack (fmtTime tdyBeg)
            , ""
            , "currHour:    " ++ show currHour
            , "targetHrs:   " ++ show targetHrs
            , "todayHrs:    " ++ show todayHrs
            , "realHrs:     " ++ show realHrs
            , "hoursLeft:   " ++ show hoursLeft
            , "discrep:     " ++ show discrep
            , ""
            , "period:      " ++ show per
            , "days:        " ++ show (floor (diffUTCTime end beg / 3600 / 24))
            , "isWeekend:   " ++ show isWeekend
            , "workHrs:     " ++ show workHrs
            , "targHrs:     " ++ show targHrs
            , ""
            , "indicator:   " ++ show indicator
            , "paceMark:    " ++ show paceMark
            , ""
            , "length is:   " ++ show (length is)
            , "length os:   " ++ show (length os)
            , "loggedIn:    " ++ show loggedIn
            ]

    liftIO $ printf "%s%.1fh (%.1fh) %.1f%%%s\n"
        (T.unpack indicator) (abs discrep) hoursLeft paceMark
        (if loggedIn
         -- then printf "\n\ESC[37mὕ3\ESC[0m %.2fh" todayHrs
         then printf "\nὕ3%.2fh" todayHrs
         else T.unpack "")

-- Main.hs (hours) ends here
