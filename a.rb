#!/bin/bash
git bisect start
git bisect bad HEAD
git bisect good last-known-good
exec git bisect run nix-build '<darwin>' -A pkgs.$1
