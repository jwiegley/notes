# Set the variable NIX_PATH to point to the directory where you've cloned the
# nixpkgs repository.  Then you can run one of two commands:
#
#   nix-build -A crashEnv
#
# This puts a script called 'load-env-crashEnv' into ./result/bin.  Running
# that script puts you into a shell where you can use all of the crash-related
# binaries.
#
#   nix-shell -A crash.safeIsa
#
# This puts you into a shell where you can work on a crash component.  The
# only special thing to note is that instead of calling 'cabal configure', you
# must use:
#
#   eval "$configurePhase"
#
# You are free to use "cabal build" for building, and "cabal test".  Do not
# use "cabal install", as it won't put the binaries anywhere that you will
# find them.  It's best to use what you build directly from the ./dist/build
# directory.
#
# If you ever need to configure again, or if cabal build tries to configure
# again, you must first run:
#
#   unset GHC_PACKAGE_PATH

{ pkgs ? (import <nixpkgs> { config = {
    allowUnfree = true;         # because we haven't set license params
  };})
}:

let
  haskellPkgs = pkgs.haskellPackages_ghc784;

  inherit (pkgs) stdenv;
  inherit (haskellPkgs) disableTest;

  callPackage = stdenv.lib.callPackageWith
    (pkgs // haskellPkgs // haskellDeps // crash);

  crash = {
    safeIsa           = callPackage ./isa/tools/safe-isa {};
    safeSim           = callPackage ./isa/tools/safe-sim {};
    safeLib           = callPackage ./isa/code/safelib/safe-lib {};
    safeIsaTests      = callPackage ./isa/code/IsaTests/safe-isa-tests {};
    safeMeld          = callPackage ./isa/tools/safe-meld {};
    safeMeldLib       = callPackage ./isa/tools/safe-meld-lib {};
    safeScripts       = disableTest (callPackage ./isa/tools/safe-scripts {});
    languageSupport   = callPackage ./external/safe-lang-support {};
    tempestCompiler   = callPackage ./tempest/tempest-compiler {};
    simplePat         = callPackage ./applications/simple-pat/src/PATServer/haskell {};
    meldCore          = callPackage ./external/meld-core {};
    breezeCompiler    = callPackage ./external/breeze/breeze-compiler {};
    breezeCore        = callPackage ./external/breeze/breeze-core {};
    breezeInterpreter = callPackage ./external/breeze/breeze-interpreter/src {};
  };

  # Build the SAFE tools with some specific dependencies.  If we move to GHC
  # 7.8 and more modern libraries, we can delete some or all of these.
  haskellDeps = pkgs.recurseIntoAttrs {
    unbound = haskellPkgs.unbound.override { binary = haskellPkgs.binary_0_7_2_2; };
    dataPartition = callPackage ./nix/data-partition-0.2.0.1.nix {};
    eitherUnwrap  = disableTest (callPackage ./nix/either-unwrap-1.1.nix {});
    polyparse  = callPackage ./nix/polyparse-1.9.nix {};
    cpphs = haskellPkgs.cpphs.override {
      polyparse = callPackage ./nix/polyparse-1.9.nix {};
    };
    optparseApplicative = callPackage ./nix/optparse-applicative-0.9.1.1.nix {};
    transformers  =
      if pkgs.stdenv.lib.versionOlder haskellPkgs.ghc.version "7.7"
      then haskellPkgs.transformers_0_3_0_0
      else haskellPkgs.transformers;
  };

in {
  crash = crash;
  deps  = haskellDeps;

  crashEnv = with haskellPkgs; with crash; pkgs.myEnvFun {
    name = "crash";
    buildInputs = stdenv.lib.attrValues crash ++ [
      ghc cabalInstall alex happy
    ];
  };

  # This is all you need to run the IsaTests:
  #
  #   nix-build -j4 -A crashTestEnv
  #   ./result/bin/load-env-crashTest
  #   cd src
  #   make clean
  #   make -j8
  #   cd ../isa/code/IsaTests
  #   make clean
  #   make asms-fast
  #   make safe-sim-fast

  crashTestEnv = with haskellPkgs; with crash; pkgs.myEnvFun {
    name = "crashTest";
    buildInputs = [ safeIsa safeSim safeScripts ] ++ [
      ghc cabalInstall alex happy
    ];
  };
}
