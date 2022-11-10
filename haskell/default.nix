{ ghcCompiler ? "ghc924"
, pkgs ? (import <darwin> {}).pkgs
, returnShellEnv ? pkgs.lib.inNixShell
, mkDerivation ? null
}:

let

haskellPackages = pkgs.haskell.packages.${ghcCompiler};

in haskellPackages.developPackage {
  root = ./.;

  overrides = with pkgs.haskell.lib; self: super: {};

  source-overrides = {};

  modifier = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
    buildTools = (attrs.buildTools or []) ++ [
      haskellPackages.cabal-install
    ];

    enableLibraryProfiling = false;
  });

  inherit returnShellEnv;
}


