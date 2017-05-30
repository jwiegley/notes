17:08:49 [9.027s] Vulcan $ nix-build '<nixpkgs>' -A haskPkgs.derive
these derivations will be built:
  /nix/store/2wgjpkjqm6zxxfy9gq3lf4bivm0jf0i0-derive-2.5.26.drv
building path(s) ‘/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26’
setupCompilerEnvironmentPhase
Build with /nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2.
unpacking sources
unpacking source archive /nix/store/ljvqvsmb4ayzj7spq4ck76a5gj8sy2wb-derive
source root is derive
patching sources
Run jailbreak-cabal to lift version restrictions on build inputs.
compileBuildDriverPhase
setupCompileFlags: -package-db=/private/var/folders/ds/nt2q1_s57cqgt9g94_vmkjcw0000gn/T/nix-build-derive-2.5.26.drv-0/package.conf.d -j8 -threaded
[1 of 1] Compiling Main             ( Setup.hs, /private/var/folders/ds/nt2q1_s57cqgt9g94_vmkjcw0000gn/T/nix-build-derive-2.5.26.drv-0/Main.o )
Linking Setup ...

In file included from /private/var/folders/ds/nt2q1_s57cqgt9g94_vmkjcw0000gn/T/nix-build-derive-2.5.26.drv-0/ghc47440_0/ghc_4.c:1:0: error:


In file included from /nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/Rts.h:217:0: error:


/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:505:5: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]
#if ZERO_SLOP_FOR_LDV_PROF || ZERO_SLOP_FOR_SANITY_CHECK
    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:502:37: error:
     note: expanded from macro 'ZERO_SLOP_FOR_LDV_PROF'
#define ZERO_SLOP_FOR_LDV_PROF     (defined(PROFILING))
                                    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:505:31: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]
#if ZERO_SLOP_FOR_LDV_PROF || ZERO_SLOP_FOR_SANITY_CHECK
                              ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:503:37: error:
     note: expanded from macro 'ZERO_SLOP_FOR_SANITY_CHECK'
#define ZERO_SLOP_FOR_SANITY_CHECK (defined(DEBUG) && !defined(THREADED_RTS))
                                    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:505:31: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:503:56: error:
     note: expanded from macro 'ZERO_SLOP_FOR_SANITY_CHECK'
#define ZERO_SLOP_FOR_SANITY_CHECK (defined(DEBUG) && !defined(THREADED_RTS))
                                                       ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:523:5: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]
#if ZERO_SLOP_FOR_LDV_PROF && !ZERO_SLOP_FOR_SANITY_CHECK
    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:502:37: error:
     note: expanded from macro 'ZERO_SLOP_FOR_LDV_PROF'
#define ZERO_SLOP_FOR_LDV_PROF     (defined(PROFILING))
                                    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:523:32: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]
#if ZERO_SLOP_FOR_LDV_PROF && !ZERO_SLOP_FOR_SANITY_CHECK
                               ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:503:37: error:
     note: expanded from macro 'ZERO_SLOP_FOR_SANITY_CHECK'
#define ZERO_SLOP_FOR_SANITY_CHECK (defined(DEBUG) && !defined(THREADED_RTS))
                                    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:523:32: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:503:56: error:
     note: expanded from macro 'ZERO_SLOP_FOR_SANITY_CHECK'
#define ZERO_SLOP_FOR_SANITY_CHECK (defined(DEBUG) && !defined(THREADED_RTS))
                                                       ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:552:5: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]
#if ZERO_SLOP_FOR_LDV_PROF && !ZERO_SLOP_FOR_SANITY_CHECK
    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:502:37: error:
     note: expanded from macro 'ZERO_SLOP_FOR_LDV_PROF'
#define ZERO_SLOP_FOR_LDV_PROF     (defined(PROFILING))
                                    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:552:32: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]
#if ZERO_SLOP_FOR_LDV_PROF && !ZERO_SLOP_FOR_SANITY_CHECK
                               ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:503:37: error:
     note: expanded from macro 'ZERO_SLOP_FOR_SANITY_CHECK'
#define ZERO_SLOP_FOR_SANITY_CHECK (defined(DEBUG) && !defined(THREADED_RTS))
                                    ^

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:552:32: error:
     warning: macro expansion producing 'defined' has undefined behavior [-Wexpansion-to-defined]

/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/lib/ghc-8.0.2/include/rts/storage/ClosureMacros.h:503:56: error:
     note: expanded from macro 'ZERO_SLOP_FOR_SANITY_CHECK'
#define ZERO_SLOP_FOR_SANITY_CHECK (defined(DEBUG) && !defined(THREADED_RTS))
                                                       ^
9 warnings generated.
configuring
configureFlags: --verbose --prefix=/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26 --libdir=$prefix/lib/$compiler --libsubdir=$pkgid --with-gcc=clang --package-db=/private/var/folders/ds/nt2q1_s57cqgt9g94_vmkjcw0000gn/T/nix-build-derive-2.5.26.drv-0/package.conf.d --ghc-option=-optl=-Wl,-headerpad_max_install_names --ghc-option=-j8 --disable-split-objs --disable-library-profiling --disable-profiling --enable-shared --disable-coverage --enable-library-vanilla --enable-executable-dynamic --enable-tests
Configuring derive-2.5.26...
Dependency base -any: using base-4.9.1.0
Dependency bytestring -any: using bytestring-0.10.8.1
Dependency containers -any: using containers-0.5.7.1
Dependency derive -any: using derive-2.5.26
Dependency directory -any: using directory-1.3.0.0
Dependency filepath -any: using filepath-1.4.1.1
Dependency haskell-src-exts -any: using haskell-src-exts-1.18.2
Dependency pretty -any: using pretty-1.1.3.3
Dependency process -any: using process-1.4.3.0
Dependency syb -any: using syb-0.6
Dependency template-haskell -any: using template-haskell-2.11.1.0
Dependency transformers -any: using transformers-0.5.2.0
Dependency uniplate -any: using uniplate-1.6.12
Using Cabal-1.24.2.0 compiled by ghc-8.0
Using compiler: ghc-8.0.2
Using install prefix:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26
Binaries installed in:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26/bin
Libraries installed in:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26/lib/ghc-8.0.2/derive-2.5.26
Dynamic libraries installed in:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26/lib/ghc-8.0.2/x86_64-osx-ghc-8.0.2
Private binaries installed in:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26/libexec
Data files installed in:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26/share/x86_64-osx-ghc-8.0.2/derive-2.5.26
Documentation installed in:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26/share/doc/x86_64-osx-ghc-8.0.2/derive-2.5.26
Configuration files installed in:
/nix/store/g28dzdsvk77sg1dvwqg4k5fq48sz6ds7-derive-2.5.26/etc
No alex found
Using ar found on system at:
/nix/store/sb6b744nr1abknw0xsk0npscpkvdln9m-cctools-binutils-darwin/bin/ar
No c2hs found
Using cpphs version 1.20.5 found on system at:
/nix/store/9xsnp6l63jqz11wjmcd0lv2wq3cafg5x-cpphs-1.20.5/bin/cpphs
Using gcc version 4.2.1 given by user at:
/nix/store/kqp0x1ha3zycd9f99613q8sb89anjv7z-clang-wrapper-4.0.0/bin/clang
Using ghc version 8.0.2 found on system at:
/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/bin/ghc
Using ghc-pkg version 8.0.2 found on system at:
/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/bin/ghc-pkg
No ghcjs found
No ghcjs-pkg found
No greencard found
Using haddock version 2.17.3 found on system at:
/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/bin/haddock
No happy found
Using haskell-suite found on system at: haskell-suite-dummy-location
Using haskell-suite-pkg found on system at: haskell-suite-pkg-dummy-location
No hmake found
Using hpc version 0.67 found on system at:
/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/bin/hpc
Using hsc2hs version 0.68.1 found on system at:
/nix/store/5yh0b6arizbvvi7n51vv5xsk5z67am6s-ghc-8.0.2/bin/hsc2hs
Using hscolour version 1.24 found on system at:
/nix/store/iac8lw5prmxy19ay942h3ck7hiwi73c4-hscolour-1.24.1/bin/HsColour
No jhc found
Using ld found on system at:
/nix/store/kqp0x1ha3zycd9f99613q8sb89anjv7z-clang-wrapper-4.0.0/bin/ld
No lhc found
No lhc-pkg found
No pkg-config found
Using strip found on system at:
/nix/store/sb6b744nr1abknw0xsk0npscpkvdln9m-cctools-binutils-darwin/bin/strip
Using tar found on system at:
/nix/store/l4d60hcav2l2sy0ni14g8sg5mh4h2h3n-gnutar-1.29/bin/tar
No uhc found
building
Building derive-2.5.26...
Preprocessing library derive-2.5.26...
[ 1 of 64] Compiling Language.Haskell.TH.Compat ( src/Language/Haskell/TH/Compat.hs, dist/build/Language/Haskell/TH/Compat.o )
[ 2 of 64] Compiling Language.Haskell.TH.Data ( src/Language/Haskell/TH/Data.hs, dist/build/Language/Haskell/TH/Data.o )
[ 3 of 64] Compiling Language.Haskell.TH.ExpandSynonym ( src/Language/Haskell/TH/ExpandSynonym.hs, dist/build/Language/Haskell/TH/ExpandSynonym.o )
[ 4 of 64] Compiling Language.Haskell.TH.Helper ( src/Language/Haskell/TH/Helper.hs, dist/build/Language/Haskell/TH/Helper.o )
[ 5 of 64] Compiling Language.Haskell.TH.Peephole ( src/Language/Haskell/TH/Peephole.hs, dist/build/Language/Haskell/TH/Peephole.o )

src/Language/Haskell/TH/Peephole.hs:78:1: warning:
    Pattern match checker exceeded (2000000) iterations in
    an equation for ‘peep’. (Use -fmax-pmcheck-iterations=n
    to set the maximun number of iterations to n)
[ 6 of 64] Compiling Language.Haskell.TH.All ( src/Language/Haskell/TH/All.hs, dist/build/Language/Haskell/TH/All.o )
[ 7 of 64] Compiling Language.Haskell ( src/Language/Haskell.hs, dist/build/Language/Haskell.o )

src/Language/Haskell.hs:288:31: error:
    Ambiguous occurrence ‘FieldDecl’
    It could refer to either ‘Language.Haskell.Exts.FieldDecl’,
                             imported from ‘Language.Haskell.Exts’ at src/Language/Haskell.hs:4:1-57
                             (and originally defined in ‘Language.Haskell.Exts.Syntax’)
                          or ‘Language.Haskell.FieldDecl’,
                             defined at src/Language/Haskell.hs:210:1
[10 of 64] Compiling Data.Derive.Internal.Instance ( src/Data/Derive/Internal/Instance.hs, dist/build/Data/Derive/Internal/Instance.o )
[51 of 64] Compiling Data.Derive.Class.Default ( src/Data/Derive/Class/Default.hs, dist/build/Data/Derive/Class/Default.o )
[52 of 64] Compiling Data.Derive.Class.Arities ( src/Data/Derive/Class/Arities.hs, dist/build/Data/Derive/Class/Arities.o )
[53 of 64] Compiling Data.Derive.Instance.Arities ( src/Data/Derive/Instance/Arities.hs, dist/build/Data/Derive/Instance/Arities.o )
builder for ‘/nix/store/2wgjpkjqm6zxxfy9gq3lf4bivm0jf0i0-derive-2.5.26.drv’ failed with exit code 1
error: build of ‘/nix/store/2wgjpkjqm6zxxfy9gq3lf4bivm0jf0i0-derive-2.5.26.drv’ failed
✔ ~/oss/morphdb [develop|✔]
17:09:06 [9.168s] Vulcan $