{ compiler    ? "ghc822"

, doProfiling ? false
, doBenchmark ? false

, rev         ? "ee28e35ba37ab285fc29e4a09f26235ffe4123e2"
, sha256      ? "0a6xrqjj2ihkz1bizhy5r843n38xgimzw5s2mfc42kk2rgc95gw5"
, nixpkgs     ? import (builtins.fetchTarball {
    url    = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    sha256 = sha256; }) { config.allowBroken = false; config.allowUnfree = true; }
}:

let

  inherit (nixpkgs) pkgs;

  haskellPackages = let hpkgs = pkgs.haskell.packages.${compiler}; in
    hpkgs // {
      mkDerivation = args: hpkgs.mkDerivation (args // {
        enableLibraryProfiling = doProfiling;
        enableExecutableProfiling = doProfiling;
      });
    };

  pkg = haskellPackages.developPackage {
    root = ./.;
    overrides = with pkgs.haskell.lib; self: super: {
      conduit       = super.conduit_1_2_13_1;
      resourcet     = super.resourcet_1_1_11;
      conduit-extra = super.conduit-extra_1_2_3_2;
      xml-conduit   = super.xml-conduit_1_7_1_2;
      http-conduit  = super.http-conduit_2_2_4;
      text-show     = dontCheck super.text-show;

      recurseForDerivations = true;
    };
    source-overrides = {
    };
    modifier = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
      executableHaskellDepends = attrs.executableHaskellDepends ++
        [ haskellPackages.hpack haskellPackages.c2hsc ];
    });
  };

  variant = if doBenchmark
            then pkgs.haskell.lib.doBenchmark
            else pkgs.lib.id;

in variant pkg
