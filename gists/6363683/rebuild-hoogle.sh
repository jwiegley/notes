#!/bin/bash -xe

DIR=/usr/local/tools/hoogle/cabal-dev/share/hoogle-4.2.16/databases

test -d $DIR || mkdir -p $DIR
cd $DIR

export PATH=/usr/local/tools/hoogle/cabal-dev/bin/:$PATH

function import_dbs() {
    find $1 -name '*.txt' \
        | parallel 'cp -p {} .; perl -i -pe "print \"\@url file://{//}/index.html\n\" if /^\@version/;" {/}; hoogle convert {/}'
}

import_dbs ~/fpco/.hsenvs/ghc-7.4.2.9/.hsenv/cabal/share/doc
import_dbs /usr/local/opt/ghc/var/dot-cabal/share/doc

rm -f default.hoo rehoo*

time hoogle data -r -l $(echo *.txt | sed 's/\.txt//g')
time rehoo -j4 -c64 .
