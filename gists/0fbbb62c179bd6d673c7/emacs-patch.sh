#!/bin/bash

patch -p0 < $1/patch-mac
cp -pR $1/mac .
#cp nextstep/Cocoa/Emacs.base/Contents/Resources/Emacs.icns mac/Emacs.app/Contents/Resources/Emacs.icns
rsync -av $1/src/ src/
cp -pR $1/lisp/term/mac-win.el lisp/term

exit 0
