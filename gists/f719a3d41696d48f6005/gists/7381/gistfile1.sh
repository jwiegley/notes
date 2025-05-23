#!/bin/bash

commit=$1
branch=$2
if [[ -z "$branch" ]]; then
    branch=HEAD
fi

git rev-list --children $branch --not $commit^@ | \
    awk "/^$commit/ { print \$2 }"

