# Build libffi, using PR#281 on GitHub, which is a port for RISC-V
WORKDIR $RISCV
RUN git clone https://github.com/libffi/libffi.git && \
    cd libffi && \
    git fetch origin pull/281/head:pr281 && \
    git checkout pr281 && \
    sh autogen.sh && \
    ./configure --host=riscv64-unknown-linux-gnu \
                --target=riscv64-unknown-linux-gnu --prefix=$RISCV && \
    make -j $NUMJOBS install

# Build a GHC cross-compiler that can target RISCV
WORKDIR $RISCV
COPY 8.0.1.patch $RISCV
RUN curl -L http://downloads.haskell.org/~ghc/8.0.1/ghc-8.0.1-src.tar.xz | tar -xJ && \
    apt-get install -y ghc perl && \
    cd $RISCV/ghc-8.0.1 && \
    patch -p1 < $RISCV/8.0.1.patch && \
    ./configure --prefix=$RISCV --target=riscv64-unknown-linux-gnu \
                --with-ffi-includes=/opt/riscv/lib/libffi-3.99999/include \
                --with-ffi-libraries=/opt/riscv/lib --with-system-libffi \
                --enable-unregisterised && \
    perl -i -pe 's/"target arch", ""/"target arch", "ArchRISCV"/;' settings && \
    perl -i -pe 's/DYNAMIC_GHC_PROGRAMS = YES/DYNAMIC_GHC_PROGRAMS = NO/;' mk/config.mk && \
    make -j $NUMJOBS