module Fridays where

import Data.Time.Calendar
import Data.Time.Calendar.WeekDate

main =
    mapM_ print [ date | year <- [2012..2017], month <- [1..12],
                         date <- [fromGregorian year month 13],
                         let (_, _, weekDay) = toWeekDate date in weekDay == 5 ]
