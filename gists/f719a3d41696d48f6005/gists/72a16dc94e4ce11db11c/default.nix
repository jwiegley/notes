# Set the variable NIX_PATH to point to the directory where you've cloned the
# nixpkgs repository.  Then you can run one of two commands:
#
#   nix-build -A crashEnv
#
# This puts a script called 'load-env-crashEnv' into ./resault/bin.  Running
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
# You are free to use "cabal build" for building.  If you ever need to
# configure again, or if cabal build tries to configure again, you must first
# run:
#
#   unset GHC_PACKAGE_PATH

{ pkgs ? (import <nixpkgs> { config = {
    allowUnfree = true;         # because we haven't set license params
  };})
}:

let
  haskellPkgs = pkgs.haskellPackages_ghc763.profiling;

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
    languageSupport   = callPackage ./language-support {};
    tempestCompiler   = callPackage ./tempest/tempest-compiler {};
    simplePat         = callPackage ./applications/simple-pat/src/PATServer/haskell {};
    breezeCompiler    = callPackage ./breeze/breeze-compiler {};
    breezeCore        = callPackage ./breeze/breeze-core {};
    breezeInterpreter = callPackage ./breeze/breeze-interpreter/src {};
  };

  # Build the SAFE tools with some specific dependencies.  If we move to GHC
  # 7.8 and more modern libraries, we can delete some or all of these.
  haskellDeps = pkgs.recurseIntoAttrs {
    cond          = callPackage ./nix/cond-0.0.2.nix {};
    dataPartition = callPackage ./nix/data-partition-0.2.0.1.nix {};
    eitherUnwrap  = disableTest (callPackage ./nix/either-unwrap-1.1.nix {});
    lens          = disableTest (callPackage ./nix/lens-3.10.2.nix {});
    mtl           = haskellPkgs.mtl_2_1_2;
    network       = disableTest haskellPkgs.network_2_4_1_2;
    unbound       = callPackage ./nix/unbound-0.4.nix {};
    dlist         = callPackage ./nix/dlist-0.5.nix {};

    MonadCatchIOTransformers =
      callPackage ./nix/MonadCatchIO-transformers-0.3.0.0.nix {};
    optparseApplicative = callPackage ./nix/optparse-applicative-0.7.0.nix {};
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

  # This is all you need for running IsaTests:
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
