#!/bin/bash

HPC_DIR=dist/hpc
HPC_REPO_DIR=$HPC_DIR/tix
TEST_DIR=test
TIX=${HPC_REPO_DIR}/test

TEST_MODULES=(`cd ${TEST_DIR}; find . -name "*.hs"      \
                | sed -e "s/\.hs$//g"                   \
                | sed -e "s/^\.\///g"                   \
                | sed -e "s/\//\./g"`)

for ITEM in ${TEST_MODULES[@]}; do
    EXCLUDES="${EXCLUDES} --exclude ${ITEM}"
done

hpc report $TIX $EXCLUDES --hpcdir=$HPC_DIR --xml-output \
    > $HPC_REPO_DIR/result.xml
hpc markup $TIX/$(basename $TIX).tix $EXCLUDES \
    --hpcdir=$HPC_DIR --destdir=$HPC_REPO_DIR

open $HPC_REPO_DIR/hpc_index.html

exit 0

### hpc-report
