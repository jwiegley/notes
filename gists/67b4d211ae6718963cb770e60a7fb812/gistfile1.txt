#!/bin/bash

set -euo pipefail
IFS=$'\n\t'

EXE=$1
DIR=${2:-$PWD}

mkdir -p "$DIR"
cd "$DIR"

if [[ ! -x "$EXE" ]]; then
    echo "$EXE is not an executable"
fi

cp -pLv "$EXE" .

EXE=$(basename "$EXE")

function dylibs() {
    otool -L "$1" | grep '\.dylib' | grep -v ':$' | awk '{print $1}'
}

function dest_name() {
    echo "$1" | sed 's%/%_%g' | sed 's/^_//' | openssl md5 | awk '{print $2}'
}

COUNTER=1
declare -A names

function gather_deps() {
    for LIB in $(dylibs "$1"); do
        FULL=$(dest_name "$LIB")
        if [[ ! -f "${FULL}.copied" ]]; then
            touch "${FULL}.copied"

            DEST=${COUNTER}.dylib
            COUNTER=$((COUNTER + 1))

            names["$LIB"]=$DEST

            cp -pLv "$LIB" "$DEST"
            gather_deps "$DEST"
        fi
    done
}

gather_deps "$EXE"

rm -f *.copied

chmod u+w *

function fix_refs() {
    install_name_tool -id "@executable_path/$1" "$1"

    for LIB in $(dylibs "$1"); do
        if [[ ! $LIB =~ executable_path ]]; then
            DEST=${names["$LIB"]}
            EPATH="@executable_path/$DEST"
            echo "patching $LIB -> $EPATH"

            install_name_tool -change "$LIB" "$EPATH" "$1"

            if [[ ! -f "${DEST}.done" ]]; then
                touch "${DEST}.done"
                fix_refs "$DEST"
            fi
        fi
    done
}

fix_refs "$EXE"

rm -f *.done
