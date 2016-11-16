#!/bin/bash

nix-push --dest ~/Products/nix-binary-cache --link --key-file ~/.nix/sk \
         --manifest --url-prefix http://ftp.newartisans.com/pub/nix-binary-cache \
         $(readlink -f ~/.nix-profile)
(cd ~/.nix-defexpr/nixpkgs ; git rev-parse HEAD) > ~/Products/nix-binary-cache/commit.txt
exec rsync -aP --delete ~/Products/nix-binary-cache/ jw3:/srv/ftp/pub/nix-binary-cache/
