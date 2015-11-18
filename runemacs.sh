#!/bin/sh

basedir=$HOME/.emacs.d/devel

export EMACSDATA=$basedir/etc
export EMACSDOC=$basedir/build/etc
export EMACSLOADPATH=$basedir/lisp
#export EMACSPATH=
export INFOPATH=$basedir/info:$INFOPATH

gdb $basedir/build/nextstep/Emacs.app/Contents/MacOS/Emacs
