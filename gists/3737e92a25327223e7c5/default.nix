# Set the variable NIX_PATH to point to the directory where you've cloned the
# nixpkgs repository.  Then run either:
#
#  nix-build
#
# This puts the resulting binaries into a directory which is symlinked to
# "result" in the current directory.  Note however that this builds everything
# sub-project that has changes each time, and not only the files that need
# building, so it's not as useful for day-to-day development.  It is a good
# way to prove that everything will build together on another machine, though.
#
#  nix-shell
#
# This puts you into a shell where you can work on crash using regular cabal.
# All of the tools and dependencies you need will be in scope, and at the
# right versions.  You won't use 'make' at the top level, but rather cabal
# install in each of the sub-projects.  Thus, if we do decide to use Nix, we
# should rewrite the Makefile according.

{ pkgs ? (import <nixpkgs> { config = {
    allowUnfree = true;         # because we haven't set the license params
    packageOverrides = pkgs: rec { haskellPackages =
      pkgs.recurseIntoAttrs (pkgs.haskellPackages_ghc763.profiling.override {
        # Crash must build using GHC 7.6.3, and with certain other
        # dependencies fixed at specific versions.  We override those
        # library here, so that all transitive dependencies build with
        # those versions as well.
        extension = self: hp: {
          mtl     = hp.mtl_2_1_2;
          network = hp.disableTest hp.network_2_4_1_2;
        };
      });
    };
  };})
}:

let
  inherit (pkgs) stdenv;
  inherit (pkgs.haskellPackages) disableTest;

  callPackage = stdenv.lib.callPackageWith
    (pkgs // pkgs.haskellPackages // haskellDeps // crash);

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

  # Build the SAFE tools with some very specific dependencies.  If we ever
  # move to GHC 7.8.2 and more modern libraries, then we can delete some or
  # all of these.
  haskellDeps = {
    eitherUnwrap  = disableTest (callPackage ./nix/either-unwrap-1.1.nix {});
    cond          = callPackage ./nix/cond-0.0.2.nix {};
    hoopl         = callPackage ./nix/hoopl-3.9.0.0.nix {};
    dataPartition = callPackage ./nix/data-partition-0.2.0.1.nix {};
    lens          = disableTest (callPackage ./nix/lens-3.10.2.nix {});
    unbound       = callPackage ./nix/unbound-0.4.nix {};
    dlist         = callPackage ./nix/dlist-0.5.nix {};

    optparseApplicative = callPackage ./nix/optparse-applicative-0.7.0.nix {};
    MonadCatchIOTransformers =
      callPackage ./nix/MonadCatchIO-transformers-0.3.0.0.nix {};
  };

in {
  crash = crash;

  crashTestEnv = with pkgs.haskellPackages; with crash; pkgs.myEnvFun rec {
    name = "crashTest";
    buildInputs = [ safeIsa safeSim safeIsaTests safeScripts ] ++ [
      ghc cabalInstall alex happy
    ];
  };

  crashEnv = with pkgs.haskellPackages; with crash; pkgs.myEnvFun rec {
    name = "crash";
    buildInputs = stdenv.lib.attrValues crash ++ [
      ghc cabalInstall alex happy
    ];
  };
}
