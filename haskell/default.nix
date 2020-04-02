{ compiler ? "ghc882"

, rev    ? "8da81465c19fca393a3b17004c743e4d82a98e4f"
, sha256 ? "1f3s27nrssfk413pszjhbs70wpap43bbjx2pf4zq5x2c1kd72l6y"

, pkgs ?
    if builtins.compareVersions builtins.nixVersion "2.0" < 0
    then abort "hnix requires at least nix 2.0"
    else import (builtins.fetchTarball {
           url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
           inherit sha256; }) {
           config.allowUnfree = true;
           config.allowBroken = false;
         }
, returnShellEnv ? pkgs.lib.inNixShell
, mkDerivation ? null
}:

let

haskellPackages = pkgs.haskell.packages.${compiler};

drv = haskellPackages.developPackage {
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
};

in drv
