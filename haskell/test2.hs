{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.Exception
import IdeSession
import Data.Function
import Prelude hiding (catch)

main = do
    sess <- initSession defaultSessionConfig
                { configDir             = "."
                , configGenerateModInfo = True
                }

    let cb = \_ -> return ()
        update = flip (updateSession sess) cb

    update $ updateCodeGeneration True
    update $ updateStdoutBufferMode (RunLineBuffering Nothing)
    update $ updateStderrBufferMode (RunLineBuffering Nothing)

    update $ updateModule "A.hs"
        "module A where\n\
        \\n\
        \main = putStrLn \"Hello!\"\n"

    print =<< getSourceErrors sess

    putStrLn "Running with module B (which does not exist)"
    catch (callRunWait =<< runStmt sess "B" "main")
        $ \e -> putStrLn (show (e :: SomeException))

    putStrLn "Running with module A"
    catch (callRunWait =<< runStmt sess "A" "main")
        $ \e -> putStrLn (show (e :: SomeException))

    putStrLn "Done."

  where
    callRunWait ra = do
        ebs <- runWait ra
        case ebs of
            Left bs -> putStrLn (show bs) >> callRunWait ra
            Right rr -> print rr
