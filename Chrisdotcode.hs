{-# LANGUAGE OverloadedStrings #-}

module Chrisdotcode where

import Git
import Git.Libgit2

main = lgWithRepository "." defaultOpts $ do
    flip traverseCommits "HEAD^6" $ \oid -> do
        c <- lookupCommit oid
        print $ contributor c

contributor :: Commit -> Text
contributor (Commit { commitAuthor = c }) = c
