{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

import Control.Applicative
import Data.List(sort)
import Control.Monad
import Shelly
import System.Directory
import Data.Text
default (Text)


bookPath = "/home"

main = shelly $ verbosely $ do
    --fnames<-liftIO $ getDirectoryContents bookPath
    fnames <- Shelly.find bookPath
    forM_ fnames $ \n-> liftIO $ putStrLn $ changeName $ unpack $ toTextIgnore n where
        changeName oldname =( Prelude.take  (Prelude.length oldname - 4) oldname ) ++ "txt"
