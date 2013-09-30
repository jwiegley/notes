#!/bin/bash

PRODUCTS=~/Products

major=4.7
minor=0

export PATH=/usr/bin:/bin

if [[ ! -d "$PRODUCTS/gcc-${major}" ]]; then
    mkdir -p "$PRODUCTS/gcc-${major}"
fi
cd "$PRODUCTS/gcc-${major}"

#sudo /opt/local/bin/port deactivate -f libiconv

export AR_FOR_TARGET=/usr/bin/ar
export AS_FOR_TARGET=/usr/bin/as
export LD_FOR_TARGET=/usr/bin/ld
export NM_FOR_TARGET=/usr/bin/nm
export OBJDUMP_FOR_TARGET=/usr/bin/objdump
export RANLIB_FOR_TARGET=/usr/bin/ranlib
export STRIP_FOR_TARGET=/usr/bin/strip
export OTOOL=/usr/bin/otool
export OTOOL64=/usr/bin/otool

#    --enable-fully-dynamic-string               \

/usr/local/src/gcc/configure                    \
    --disable-multilib                          \
    --disable-nls                               \
    --enable-languages=c,c++                    \
    --enable-stage1-checking                    \
    --prefix=/usr/local/stow/gcc-${major}       \
    --program-suffix=-mp-${major}               \
    --with-gmp=/opt/local                       \
    --with-libiconv-prefix=/opt/local		\
    --with-mpc=/opt/local                       \
    --with-mpfr=/opt/local                      \
    --with-system-zlib                          \
    CPPFLAGS="-I/opt/local/include -D_GLIBCXX_FULLY_DYNAMIC_STRING=1" \
    2>&1 | tee gcc-rebuild.log

make CPPFLAGS="-I/opt/local/include -D_GLIBCXX_FULLY_DYNAMIC_STRING=1" \
    "$@" 2>&1 | tee gcc-rebuild.log

#sudo /opt/local/bin/port activate libiconv

exit 0
