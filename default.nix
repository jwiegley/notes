    make -j$NIX_BUILD_CORES -C src/reification
    make -j$NIX_BUILD_CORES -C src
    make -j$NIX_BUILD_CORES -C src native
    make -j$NIX_BUILD_CORES -C platform
    make -j$NIX_BUILD_CORES -C platform -f Makefile.cito
