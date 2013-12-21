#!/bin/bash

ext=$1

cd ~/build

rsync -aL --delete fpco/ fpco-$ext/

cd ~/build/fpco-$ext

perl -i -pe "s~/build/fpco/~/build/fpco-$ext/~g;"       \
    .hsenvs/*/.hsenv/bin/activate                       \
    .hsenvs/*/.hsenv/bin/cabal                          \
    .hsenvs/*/.hsenv/cabal/config

source dev-scripts/activate-hsenv.sh > /dev/null

"$@"
