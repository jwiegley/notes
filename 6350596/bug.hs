{-# LANGUAGE OverloadedStrings #-}

module Main where

import IdeSession
import Data.Function

main = do
    sess <- initSession defaultSessionInitParams defaultSessionConfig

    let cb = \_ -> return ()
        update = flip (updateSession sess) cb

    update $ updateCodeGeneration True
    update $ updateStdoutBufferMode (RunLineBuffering Nothing)
    update $ updateStderrBufferMode (RunLineBuffering Nothing)

    update $ updateModule "src/Main.hs"
        "module Main where\n\
        \\n\
        \שלום :: String\n\
        \שלום = \"hello\"\n\
        \\n\
        \main = putStrLn $ show שלום\n"
    print =<< getSourceErrors sess

    callRunWait =<< runStmt sess "Main" "main"

  where
    callRunWait ra = do
        ebs <- runWait ra
        case ebs of
            Left bs -> putStrLn (show bs) >> callRunWait ra
            Right rr -> print rr
