module Main where

import Control.Monad
import Git
import Git.Libgit2
import Filesystem.Path.CurrentOS
import Data.Text

main :: IO ()
main = void $ withLibGitDo $
       withRepository lgFactory (fromText (pack "/tmp/blah.git")) $
           getRepository lgFactory
