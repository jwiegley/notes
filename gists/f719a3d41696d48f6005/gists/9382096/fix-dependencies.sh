#!/bin/bash

(cabal configure --enable-tests && cabal build) > /tmp/build.out 2>&1

pkg=$(cat /tmp/build.out | perl -ne "print \"\$1\n\" if /hidden package \`(.*?)(-[0-9]+.*)?'/")
while [[ $pkg != "" ]]; do
    echo "Restoring $pkg dependency"
    perl -i -pe "s/-- , $pkg( |\$)/, $pkg\$1/;" *.cabal
    (cabal configure --enable-tests && cabal build) > /tmp/build.out 2>&1
    pkg=$(cat /tmp/build.out | perl -ne "print \"\$1\n\" if /hidden package \`(.*?)(-[0-9]+.*)?'/")
done
