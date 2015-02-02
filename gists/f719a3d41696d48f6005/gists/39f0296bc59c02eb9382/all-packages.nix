  gccApple =
    assert stdenv.isDarwin;
    wrapGCC (makeOverridable (import ../development/compilers/gcc/4.2-apple64) {
      inherit fetchurl noSysDirs;
      profiledCompiler = true;
      # Since it fails to build with GCC 4.6, build it with the "native"
      # Apple-GCC.
      stdenv = allStdenvs.stdenvNative;
    });
