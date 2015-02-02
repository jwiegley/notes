#!/bin/bash -xe
eval "$configurePhase"
unset GHC_PACKAGE_PATH
eval "$buildPhase"
eval "$checkPhase"
