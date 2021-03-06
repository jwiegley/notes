#!/bin/sh

find .git/objects -type f | \
while read file; do
    if echo $file | egrep -q '\.idx$'; then
        git show-index < $file | awk '{print $2}'
    elif echo $file | egrep -q '[0-9a-f]{38}'; then
        echo $(basename $(dirname $file))$(basename $file)
    fi
done | \
while read hash; do
    if [ "$(git cat-file -t $hash)" = commit ]; then
        echo $hash
    fi
done
