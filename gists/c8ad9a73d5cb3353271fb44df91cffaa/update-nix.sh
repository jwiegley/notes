#!/bin/bash -ex

if [[ "$1" == "-a" ]]; then
    shift 1
    cd ~/.nix-defexpr/nixpkgs-next
    git pull
    nix-env -f '<nixpkgs-next>' -u "$@"
    rsync -a --delete ~/.nix-defexpr/nixpkgs-next/ ~/.nix-defexpr/nixpkgs/
    exec push-nix
else
    nix-env -q | sed 's/-[0-9].*//' | xargs nix-env -f '<nixpkgs>' "$@" -u
fi
