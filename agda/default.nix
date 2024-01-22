{ rev      ? "f0326542989e1bdac955ad6269b334a8da4b0c95"
, sha256   ? "1p7vxlwdnhnhg287dp7n890806yi1mmxad0qgfi5f1pr1pgw8pkf"
, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/jwiegley/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
    overlays = [];
  }
}:

let
  haskellPackages = pkgs.haskell.packages.ghc8107;

  agda2hs =
    haskellPackages.developPackage rec {
      name = "agda2hs";
      root = pkgs.fetchFromGitHub {
        owner = "agda";
        repo = "agda2hs";
        rev = "984821ab84b33917a1709c36bf66a0732ebbb46d";
        sha256 = "1kgfwh5wp85gw3chvnqdkh0h063ifgwj6vwa5s8yrls5h3jzwgj1";
        # date = 2024-01-17T10:14:42+01:00;
      };

      source-overrides = {};
      overrides = self: super: with pkgs.haskell.lib; {};

      modifier = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
        buildTools = (attrs.buildTools or []) ++ [
          haskellPackages.cabal-install
        ];

        passthru = {
          nixpkgs = pkgs;
          inherit haskellPackages;
        };
      });

      returnShellEnv = false;
    };

  agda2hs-lib = pkgs.stdenv.mkDerivation rec {
    name = "agda2hs-${version}";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda2hs";
      rev = "984821ab84b33917a1709c36bf66a0732ebbb46d";
      sha256 = "1kgfwh5wp85gw3chvnqdkh0h063ifgwj6vwa5s8yrls5h3jzwgj1";
      # date = 2024-01-17T10:14:42+01:00;
    };

    buildInputs = [
      (pkgs.agdaPackages.agda.withPackages (p: [p.standard-library]))
    ];

    libraryFile = "${libraryName}.agda-lib";
    libraryName = "agda2hs";

    phases = [ "unpackPhase" "patchPhase" "buildPhase" "installPhase" ];

    buildPhase = ''
      agda -i lib lib/Haskell/Prelude.agda
    '';

    installPhase = ''
      mkdir -p $out
      cp -pR * $out
    '';
  };

in

pkgs.stdenv.mkDerivation rec {
  name = "agda-notes-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [
    pkgs.which
    # agda2hs
    (haskellPackages.ghcWithPackages (p: [
       p.lens
     ]))
    (pkgs.agdaPackages.agda.withPackages (p: [
       p.standard-library p.agda-categories # agda2hs-lib
     ]))
  ];

  libraryFile = "${libraryName}.agda-lib";
  libraryName = "notes";

  phases = [ "unpackPhase" "patchPhase" "buildPhase" "installPhase" ];

  buildPhase = ''
    cp $(which agda) ./agda2hs
    sed -i -e 's%/nix/store.*/bin/agda%agda2hs%' agda2hs
    ./agda2hs Zipper.agda || ./agda2hs Zipper.agda
    sed -i -e 's/survey ::/survey :: forall a./' Zipper.hs
    sed -i -e 's/surveyM ::/surveyM :: forall m a./' Zipper.hs
    sed -i -e 's/mapUntils ::/mapUntils :: forall a b./' Zipper.hs
    ghc -c Zipper.hs
  '';

  installPhase = ''
    mkdir $out
    cp -p Zipper.hs $out
  '';

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
