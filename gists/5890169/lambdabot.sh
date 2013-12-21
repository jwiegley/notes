#!/bin/bash

GHC_VER=7.4.2.9

LAMBDABOT=/usr/local/tools/lambdabot

export XS=$LAMBDABOT/cabal-dev/packages-${GHC_VER}.conf
export XS=$XS:/usr/local/Cellar/ghc/${GHC_VER}/lib/ghc-${GHC_VER}/package.conf.d
export GHC_PACKAGE_PATH=$XS

cd $LAMBDABOT/cabal-dev/bin
export PATH=$PWD:$PATH

exec ./lambdabot "$@"
