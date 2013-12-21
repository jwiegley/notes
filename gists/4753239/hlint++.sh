#!/bin/bash -e

egrep -n '\<(undefined|error|throw)\>' "$1" \
    | while read line; do
    linenum=$(echo "$line" | perl -pe 's/^([0-9]+:).+/\1/;')
    linerem=$(echo "$line" | perl -pe 's/^[0-9]+://;')
    echo "$1:$linenum Warning: Possible partial function"
    echo
done

egrep -n '\<(unsafe[a-zA-Z]+)\>' "$1" \
    | while read line; do
    linenum=$(echo "$line" | perl -pe 's/^([0-9]+:).+/\1/;')
    linerem=$(echo "$line" | perl -pe 's/^[0-9]+://;')
    echo "$1:$linenum Warning: Dangerous use of unsafe function"
    echo
done

egrep -n '\<(jww)\>' "$1" \
    | while read line; do
    linenum=$(echo "$line" | perl -pe 's/^([0-9]+:).+/\1/;')
    linerem=$(echo "$line" | perl -pe 's/^[0-9]+://;')
    echo "$1:$linenum Warning: Unaddressed TODO comment"
    echo
done

ghc -Wall                                       \
    -fwarn-tabs                                 \
    -fwarn-incomplete-record-updates            \
    -fwarn-monomorphism-restriction             \
    -fwarn-unused-do-bind                       \
    -fwarn-implicit-prelude                     \
    -i. -i.. -i../.. -v0 -c -fforce-recomp "$1"

hlint -u "$1"

exit 0
