args@{ coqPackages ? "coqPackages_8_15"

, rev    ? "c74fa74867a3cce6ab8371dfc03289d9cc72a66e"
, sha256 ? "13bnmpdmh1h6pb7pfzw5w3hm6nzkg9s1kcrwgw1gmdlhivrmnx75"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${coqPackages};

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
      rev = "98f6bdd5b9931a68739819823ac81e275087c73c";
      sha256 = "1srdg3ivfirpl50y4wq961ksymasd62v3vb0xd7dywllvdxb9d6m";
      # date = 2021-08-02T21:13:14-07:00;
    };

    buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
    enableParallelBuilding = true;

    preBuild = ''
      export MAKEFLAGS="-j $NIX_BUILD_CORES"
      coq_makefile -f _CoqProject -o Makefile
    '';

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.10" "8.11" "8.12" "8.13" ];
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
    equations category-theory #fiat-core coq-haskell
  ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.10" "8.11" "8.12" "8.13" ];
 };
}
