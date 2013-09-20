{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Main where

import Control.Monad
import Control.Monad.Logger as Log
import Criterion
import Criterion.Main
import Data.Text as T
import Data.Text.Encoding as T
import Data.Time
import Data.Reflection
import Language.Haskell.TH.Syntax
import System.Locale
import System.Log.FastLogger

logger :: Loc -> LogSource -> LogLevel -> LogStr -> IO ()
logger _loc src lvl str = do
    now <- getCurrentTime
    let stamp = formatTime defaultTimeLocale "%b-%d %H:%M:%S" now

    return ()
    -- putStrLn $ stamp ++ " " ++ renderLevel lvl ++ " "
    --         ++ renderSource src ++ T.unpack (renderLogStr str)
  where
    renderLevel LevelDebug       = "[DEBUG]"
    renderLevel LevelInfo        = "[INFO]"
    renderLevel LevelWarn        = "[WARN]"
    renderLevel LevelError       = "[ERROR]"
    renderLevel (LevelOther txt) = "[" ++ T.unpack txt ++ "]"

    renderSource :: Text -> String
    renderSource txt
        | T.null txt = ""
        | otherwise  = T.unpack txt ++ ": "

    renderLogStr (LS s)  = T.pack s
    renderLogStr (LB bs) = T.decodeUtf8 bs

baz :: LoggingT IO ()
baz = do $(logDebug) ""
         return ()

bar :: LoggingT IO ()
bar = baz

foo :: LoggingT IO ()
foo = bar

bazr :: Reifies s (Log.Logger IO) => RLoggingT s IO ()
bazr = do $(logDebug) ""
          return ()

barr :: Reifies s (Log.Logger IO) => RLoggingT s IO ()
barr = bazr

foor :: Reifies s (Log.Logger IO) => RLoggingT s IO ()
foor = barr

main = do
    -- runStdoutLoggingT (replicateM_ 1000000 foo)
    runStdoutRLoggingT (replicateM_ 1000000 foor)
