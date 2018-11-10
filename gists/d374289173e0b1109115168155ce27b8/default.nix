{ compiler ? "ghc843"

, doBenchmark ? false
, doTracing   ? false
, doStrict    ? false

, rev     ? "ecd9d74d973e9942574e77697cfb8db6c76d1764"
, sha256  ? "1qziyl6hjip97qx2sg9348nm38642yzkr4zg1dd90kj12aj624kz"
, pkgs    ?
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

  source-overrides = {};

  modifier = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
    buildTools = (attrs.buildTools or []) ++ [
      pkgs.wabt
      haskellPackages.happy
      haskellPackages.alex
      # haskellPackages.brittany
      # haskellPackages.stylish-haskell
    ];
  });

  inherit returnShellEnv;
};

in drv
