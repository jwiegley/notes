{ rev      ? "a3a23d9599b0a82e333ad91db2cdc479313ce154"
, sha256   ? "05xmgrrnw6j39lh3d48kg064z510i0w5vvrm1s5cdwhdc2fkspjq"
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
        rev = "160478a51bc78b0fdab07b968464420439f9fed6";
        sha256 = "13k2lcljgq0f5zbbyyafx1pizw4ln60xi0x0n0p73pczz6wdpz79";
        # date = 2021-09-08T18:00:00+02:00;
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
      rev = "160478a51bc78b0fdab07b968464420439f9fed6";
      sha256 = "13k2lcljgq0f5zbbyyafx1pizw4ln60xi0x0n0p73pczz6wdpz79";
      # date = 2021-09-08T18:00:00+02:00;
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
    agda2hs
    (haskellPackages.ghcWithPackages (p: [
       p.lens
     ]))
    (pkgs.agdaPackages.agda.withPackages (p: [
       p.standard-library p.agda-categories agda2hs-lib
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
