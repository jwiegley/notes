#!/bin/bash

if [[ -d /Volumes/Vault/Projects ]]; then
    pushme "$@" vault &
fi

if [[ -d "/Volumes/Macintosh HD 1/Users/johnw/Projects" ]]; then
    pushme "$@" clone &
fi

if [[ -d "/Volumes/My Passport/Vault" ]]; then
    pushme "$@" passport &
fi

if [[ -d "/Volumes/My Book/Vault" ]]; then
    pushme "$@" mybook &
fi

if quickping 192.168.9.133; then
    pushme "$@" titan &
fi

if [[ $(hostname) = "Vulcan.local" ]] && quickping 192.168.9.114; then
    pushme "$@" hermes &
    nix-copy-closure --to hermes $(readlink -f ~/.nix-profile) &
fi

(sudo cleanup -u; sudo cleanup -u; sudo cleanup -u) > /dev/null 2>&1

wait

### pushall ends here
