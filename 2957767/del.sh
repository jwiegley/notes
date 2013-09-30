#!/bin/bash -x

function move_to_trash {
    path="$1"
    trash="$2"

    if test -L "$path"; then
        /bin/rm -f "$path"      # don't trash symlinks, just remove them
    else
        target="$trash"/$(basename "$path")
        if test -e "$target"; then
            for (( index=$$ ; 1; index=index+1 )); do
                target="$target"-"$index"
                if ! test -e "$target"; then
                    break
                fi
            done
        fi
        mv -f "$path" "$target" # don't worry about race-condition overwrites
    fi
}

for item in "$@"; do
    if [[ -n "$item" && ${item:0:1} == '-' ]]; then
        continue
    elif ! test -e "$item"; then
        continue
    else
        target=$(realpath "$item")
        if [[ "$target" =~ ^/Volumes/([^/]+)/ ]]; then
            move_to_trash "$item" "/Volumes/${BASH_REMATCH[1]}/.Trashes/$EUID"
        else
            move_to_trash "$item" "$HOME/.Trash"
        fi
    fi
done
