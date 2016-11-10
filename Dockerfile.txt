# Build a GHC cross-compiler that can target RISCV
WORKDIR $RISCV
RUN git clone https://github.com/bgamari/llvm.git && \
    cd $RISCV/llvm && \
    git checkout -b riscv-trunk-ghc origin/riscv-trunk-ghc && \
    git submodule update --init && \
    mkdir build && \
    cd build && \
    cmake -DCMAKE_INSTALL_PREFIX=$RISCV -DLLVM_TARGETS_TO_BUILD="RISCV" ../ && \
    make -j $NUMJOBS && make install

WORKDIR $RISCV
RUN git clone https://github.com/bgamari/ghc.git && \
    git checkout -b riscv origin/riscv && \
    git submodule update --init && \
    ./configure --prefix=$RISCV --target=riscv64-unknown-linux-gnu \
                --with-ffi-includes=/opt/riscv/lib/libffi-3.99999/include \
                --with-ffi-libraries=/opt/riscv/lib --with-system-libffi && \
    cp mk/build.mk.sample mk/build.mk && \
    perl -i -pe 's/^#BuildFlavour = quick/BuildFlavour = quick/;' mk/build.mk && \
    perl -i -pe 's/^HADDOCK_DOCS = YES/HADDOCK_DOCS = NO/;' mk/build.mk && \
    perl -i -pe 's/"target arch", ""/"target arch", "ArchRISCV"/;' settings && \
    perl -i -pe 's/DYNAMIC_GHC_PROGRAMS = YES/DYNAMIC_GHC_PROGRAMS = NO/;' mk/config.mk && \
    make -j $NUMJOBS
