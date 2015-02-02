# Set the variable NIX_PATH to point to the directory where you've cloned the
# nixpkgs repository.  Then run either:
#
#    nix-build
#
# Which puts the resulting binaries into "result" in the current directory.
#
#    nix-shell
#
# Which puts you into a shell where you can work on crash.  Within that shell,
# there are four commands you should be concerned with (and probably want to
# make aliases for):
#
#    eval "$configurePhase"   -- run "cabal configure", only need to do once
#    eval "$buildPhase"       -- run "cabal build"
#    eval "$checkPhase"       -- run "cabal test"
#    eval "$installPhase"     -- test running "cabal copy"

{ pkgs ? (import <nixpkgs> { config = {
    allowUnfree = true;
    packageOverrides = self: {
      mtl = self.mtl_2_1_2;
    };
}; }) }:

let
  inherit (pkgs) stdenv;
  inherit (haskellPackages) disableTest;

  callPackage = stdenv.lib.callPackageWith (pkgs // haskellDeps // crash);

  crash = {
    safeIsa         = callPackage ./isa/tools/safe-isa {};
    safeSim         = callPackage ./isa/tools/safe-sim {};
    safeLib         = callPackage ./isa/code/safelib/safe-lib {};
    safeIsaTests    = callPackage ./isa/code/IsaTests/safe-isa-tests {};
    safeMeld        = callPackage ./isa/tools/safe-meld {};
    safeMeldLib     = callPackage ./isa/tools/safe-meld-lib {};
    safeScripts     = disableTest (callPackage ./isa/tools/safe-scripts {});
    languageSupport = callPackage ./language-support {};
    tempestCompiler = callPackage ./tempest/tempest-compiler {};
  };

  # Build the SAFE tools with some very specific dependencies.  If we ever
  # move to GHC 7.8.2 and more modern libraries, then we can delete some or
  # all of these customizations.

  haskellPackages = pkgs.haskellPackages_ghc763;

  haskellDeps = haskellPackages // (with haskellPackages; rec {
    fixMtl        = x: x.override { mtl = mtl_2_1_2; };
    mtl           = mtl_2_1_2;
    parsec        = fixMtl haskellPackages.parsec;
    network       = disableTest (network_2_4_1_2.override { parsec = parsec; });
    eitherUnwrap  = disableTest (callPackage ./nix/either-unwrap-1.1.nix {});
    cond          = callPackage ./nix/cond-0.0.2.nix {};
    hoopl         = callPackage ./nix/hoopl-3.9.0.0.nix {};
    dataPartition = callPackage ./nix/data-partition-0.2.0.1.nix {};
    lens          = disableTest (callPackage ./nix/lens-3.10.2.nix {});
    RepLib        = fixMtl haskellPackages.RepLib;
    regexpr       = (fixMtl haskellPackages.regexpr).override { mtlparse = mtlparse; };
    mtlparse      = fixMtl haskellPackages.mtlparse;
    free          = fixMtl haskellPackages.free;
    regexBase     = fixMtl haskellPackages.regexBase;
    these         = fixMtl haskellPackages.these;
    unbound       = callPackage ./nix/unbound-0.4.nix {};
    dlist         = callPackage ./nix/dlist-0.5.nix {};

    optparseApplicative = callPackage ./nix/optparse-applicative-0.7.0.nix {};
    MonadCatchIOTransformers =
      callPackage ./nix/MonadCatchIO-transformers-0.3.0.0.nix {};
  });

in with haskellDeps; with crash; stdenv.mkDerivation {
  name = "crash";
  buildInputs = [ ghc cabalInstall ];
  propagatedBuildInputs = [
    safeIsa safeIsaTests safeSim safeScripts regexpr safeMeld tempestCompiler
  ];
}
