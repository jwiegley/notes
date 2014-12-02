#!/bin/bash
cd $HOME/.nix-profile/lib
exec $HOME/.nix-profile/libexec/dovecot/imap \
    -c $HOME/Messages/Dovecot/dovecot.conf "$@"
