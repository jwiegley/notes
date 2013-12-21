#!/bin/bash

set -e

DEVEL=$HOME/.emacs.d/devel

cd $DEVEL
git clean -dfx
./autogen.sh

mkdir build
mkdir target
cd build

../configure --prefix=$DEVEL/target \
    --with-ns --enable-asserts \
    CFLAGS='-g2 -ggdb' \
    CPPFLAGS=-I/opt/local/include \
    LDFLAGS=-L/opt/local/lib

nice -n 20 make "$@" bootstrap install
