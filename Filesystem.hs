{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

import           ClassyPrelude.Conduit
import qualified Data.Conduit.Filesystem as Files
import           System.FilePath.Posix

main :: IO ()
main = do
    let dir = "/Users/johnw/.ssh"
    Files.traverse False (fpFromString dir)
        $$ mapM_C (print . makeRelative dir . fpToString)
