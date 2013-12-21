#!/bin/sh

~/Products/ledger/ledger \
    --import ~/src/ledger/tools/sample.py \
    -f ~/src/ledger/doc/sample.dat \
    -t 'get_amount(xact)' \
    register

