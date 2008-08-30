#!/bin/bash

# This is a rather brainless replacement for rm that moves files to
# the Trash instead of deleting them right away.

while echo "$1" | grep -q '^-'; do
    shift 1
done

for file in "$@"; do
    if [[ -L "$file" ]]; then
	/bin/rm -f "$file"
    elif [[ -e "$file" ]]; then
	target=$(basename "$file")
	index=$$
	while [[ -e "$HOME/.Trash/$target" ]]; do
	    target=$(basename "$file")-$index
	    index=$((index + 1))
	done
	mv "$file" "$HOME/.Trash/$target" 2>&1
    fi
done | grep -v "set owner/group.*Operation not permitted"

exit 0
