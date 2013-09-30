{-# LANGUAGE OverloadedStrings #-}

module Main where

import IdeSession

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

    update $ updateModule "Foo.hs"
        "module Foo where\n\
        \\n\
        \import Bar\n\
        \\n\
        \foo = bar >> bar\n\
        \\n\
        \foobar = putStrLn \"Baz\"\n"

    update $ updateModule "Bar.hs"
        "module Bar where\n\
        \\n\
        \bar = putStrLn \"Hello, world!\"\n"

    update $ updateModule "Baz.hs"
        "module Baz where\n\
        \\n\
        \import Foo\n\
        \import Bar\n\
        \\n\
        \baz = foobar\n"

    getSourceErrors sess

    gif <- getSpanInfo sess
    print $ gif "Baz" (SourceSpan "Baz.hs" 6 8 6 9)

    update $ updateModule "Baz.hs"
        "module Baz where\n\
        \\n\
        \import Foo\n\
        \import Bar\n\
        \\n\
        \baz = foobar >>>> foo >> bar\n"

    getSourceErrors sess

    gif <- getSpanInfo sess
    print $ gif "Baz" (SourceSpan "Baz.hs" 6 8 6 9)

    update $ updateModule "Baz.hs"
        "module Baz where\n\
        \\n\
        \import Foo\n\
        \import Bar\n\
        \\n\
        \baz = foobar >> foo >> bar\n"

    getSourceErrors sess

    gif <- getSpanInfo sess
    print $ gif "Baz" (SourceSpan "Baz.hs" 6 8 6 9)
