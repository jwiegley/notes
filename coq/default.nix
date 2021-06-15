{ packages ? "coqPackages_8_10"

, rev      ? "8da81465c19fca393a3b17004c743e4d82a98e4f"
, sha256   ? "1f3s27nrssfk413pszjhbs70wpap43bbjx2pf4zq5x2c1kd72l6y"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
    overlays = [
      (self: super:
       let
         nixpkgs = { rev, sha256 }:
           import (super.fetchFromGitHub {
             owner = "NixOS";
             repo  = "nixpkgs";
             inherit rev sha256;
           }) { config.allowUnfree = true; };

         known-good-20191113_070954 = nixpkgs {
           rev    = "620124b130c9e678b9fe9dd4a98750968b1f749a";
           sha256 = "0xgy2rn2pxii3axa0d9y4s25lsq7d9ykq30gvg2nzgmdkmy375rr";
         };
       in
       {
         inherit (known-good-20191113_070954) shared-mime-info;
       })
    ];
  }
}:

with pkgs.${packages};

let
  coq-haskell = pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-haskell-${version}";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "coq-haskell";
      rev = "921bf95cabdbcb8fc0f9dfdf7c33c3530431a5a4";
      sha256 = "0am0z62lp48n5afz5ss9srlwzp51wxi8286iibik40gis7ai86sh";
      # date = 2020-01-19T15:22:16-08:00;
    };

    buildInputs = [ coq.ocaml coq.camlp5 coq.findlib coq ssreflect ];

    preBuild = "coq_makefile -f _CoqProject -o Makefile";

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    meta = with pkgs.lib; {
      homepage = https://github.com/jwiegley/coq-haskell;
      description = "A library for Haskell users writing Coq programs";
      maintainers = with maintainers; [ jwiegley ];
      platforms = coq.meta.platforms;
    };

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" "8.9" "8.10" ];
    };
  };

  category-theory = pkgs.stdenv.mkDerivation rec {
    name = "category-theory";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "category-theory";
      rev = "380ff60d34c306f7005babc3dade1d96b5eeb935";
      sha256 = "1r4v5lm090i23kqa1ad39sgfph7pfl458kh8rahsh1mr6yl1cbv9";
      # date = 2020-01-12T15:09:07-08:00;
    };

    buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
    enableParallelBuilding = true;

    buildPhase = "make JOBS=$NIX_BUILD_CORES";
    preBuild = "coq_makefile -f _CoqProject -o Makefile";
    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" "8.9" "8.10" ];
   };
  };

  fiat-core = pkgs.stdenv.mkDerivation rec {
    name = "coq-fiat-core-${coq.coq-version}-unstable-${version}";
    version = "2018-05-14";

    src = pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "fiat-core";
      rev = "5d2d1fdfba7c3ed5a3120dad2415b0bb958b6d02";
      sha256 = "190v5sz8fmdhbndknq9mkwpj3jf570gzdibww7f76g81a34v3qli";
      fetchSubmodules = true;
      # date = 2018-05-14T10:05:32-07:00;
    };

    buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib
                    pkgs.git pkgs.python27 ];
    propagatedBuildInputs = [ coq ];

    doCheck = false;

    enableParallelBuilding = true;
    buildPhase = "make -j$NIX_BUILD_CORES";

    installPhase = ''
      COQLIB=$out/lib/coq/${coq.coq-version}/
      mkdir -p $COQLIB/user-contrib/Fiat
      cp -pR src/* $COQLIB/user-contrib/Fiat
    '';

    meta = with pkgs.lib; {
      homepage = http://plv.csail.mit.edu/fiat/;
      description = "A library for the Coq proof assistant for synthesizing efficient correct-by-construction programs from declarative specifications";
      maintainers = with maintainers; [ jwiegley ];
      platforms = coq.meta.platforms;
    };

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" "8.9" "8.10" ];
    };
  };

in pkgs.stdenv.mkDerivation rec {
  name = "coq-notes";
  version = "1.0";

  src =
    if pkgs.lib.inNixShell
    then null
    else if pkgs ? coqFilterSource
         then pkgs.coqFilterSource [] ./.
         else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib
    equations coq-haskell #category-theory fiat-core
  ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
 };
}
