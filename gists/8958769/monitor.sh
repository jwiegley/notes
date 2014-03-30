#!/bin/bash
exec /usr/local/bin/multitail \
    -l "cd ~/fpco; ~/.cabal/bin/git-monitor -v -d ~/fpco --git-dir=$HOME/fpco/.git" \
    -l "cd ~/fpco/gitlib; ~/.cabal/bin/git-monitor -v -d ~/fpco/gitlib --git-dir=$HOME/fpco/gitlib/.git"
