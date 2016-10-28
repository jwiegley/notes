RUN cd $RISCV/ghc-8.0.1 && \
    patch -p1 < $RISCV/8.0.1.patch && \
    ./configure --target=riscv64-unknown-linux-gnu --enable-unregisterised && \
    perl -i -pe 's/"target arch", ""/"target arch", "ArchRISCV"/;' settings && \
    perl -i -pe 's/DYNAMIC_GHC_PROGRAMS = YES/DYNAMIC_GHC_PROGRAMS = NO/;' mk/config.mk && \
    make
