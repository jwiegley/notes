let
  hostPkgs = import <nixpkgs> {};
  pinnedPkgs = hostPkgs.fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs-channels";
    rev = "ee28e35ba37ab285fc29e4a09f26235ffe4123e2";
    sha256 = "0a6xrqjj2ihkz1bizhy5r843n38xgimzw5s2mfc42kk2rgc95gw5";
  };

in { nixpkgs ? import pinnedPkgs {}
   , compiler ? "ghc822"
   , doProfiling ? false
   , doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  haskellPackages = pkgs.haskell.packages.${compiler};

  f = haskellPackages.developPackage {
    root = ./.;
    overrides = self: super: {
      insert-ordered-containers =
        super.insert-ordered-containers.overrideDerivation (attrs: {
        name = "insert-ordered-containers-0.2.2.0";
        version = "0.2.2.0";
        src = pkgs.fetchFromGitHub {
          owner = "mightybyte";
          repo = "insert-ordered-containers";
          rev = "842b32c012e01ba1930c34c367dab9a9412c332d";
          sha256 = "182y5ffc68dgdrdkfq7w3zsj8xmig6hdnhv5wm866qcks49i2kn4";
        };
      });
    };
  };

  variant =
    if doBenchmark
    then pkgs.haskell.lib.doBenchmark
    else if doProfiling
         then pkgs.haskell.lib.doProfiling
         else pkgs.lib.id;

  drv = variant f;

in

  drv
