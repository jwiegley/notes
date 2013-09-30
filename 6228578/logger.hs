{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Monad
import Control.Monad.Logger
import Language.Haskell.TH.Syntax
import System.Log.FastLogger
import Data.Time
import System.Locale
import Data.Text as T
import Data.Text.Encoding as T

logger :: Loc -> LogSource -> LogLevel -> LogStr -> IO ()
logger _loc src lvl str = do
    now <- getCurrentTime
    let stamp = formatTime defaultTimeLocale "%b-%d %H:%M:%S" now

    putStrLn $ stamp ++ " " ++ renderLevel lvl ++ " "
            ++ renderSource src ++ T.unpack (renderLogStr str)
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

baz :: MonadLogger m => m ()
baz = do $(logDebug) ""
         return ()

bar :: MonadLogger m => m ()
bar = do $(logDebug) ""
         baz

foo :: MonadLogger m => m ()
foo = do $(logDebug) ""
         bar

main = do
    runStdoutRLoggingT $ replicateM_ 1000000 foo
