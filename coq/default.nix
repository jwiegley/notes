{ packages ? "coqPackages_8_9"

, rev      ? "d73f16d6767e99675682f822dac3017bf9af1e83"
, sha256   ? "1b5wix9kr5s3hscpl425si0zw00zzijc9xrcph6l2myh4n5nvcm0"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
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
      rev = "83a5db4b5741745ec9d522543d3616c308dfb542";
      sha256 = "0310sbf6i8zfvrw5mqaifnh4rdl0j64gj3j20ak533xpq1fpbd4v";
      # date = 2018-10-04T18:17:03-07:00;
    };

    buildInputs = [ coq.ocaml coq.camlp5 coq.findlib coq ssreflect ];

    preBuild = "coq_makefile -f _CoqProject -o Makefile";

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    meta = with pkgs.stdenv.lib; {
      homepage = https://github.com/jwiegley/coq-haskell;
      description = "A library for Haskell users writing Coq programs";
      maintainers = with maintainers; [ jwiegley ];
      platforms = coq.meta.platforms;
    };

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" ];
    };
  };

  category-theory = pkgs.stdenv.mkDerivation rec {
    name = "category-theory";
    version = "1.0";

    src = pkgs.fetchFromGitHub {
      owner = "jwiegley";
      repo = "category-theory";
      rev = "e204fee5b8662e414ecca13ca543fae3b19bd72a";
      sha256 = "15hi0vmvm42qzsh5zzw78q2l5c8bf4nis2mjbannm0m96dpmszk0";
      # date = 2018-10-05T10:50:15-07:00;
    };

    buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
    enableParallelBuilding = true;

    buildPhase = "make JOBS=$NIX_BUILD_CORES";
    preBuild = "coq_makefile -f _CoqProject -o Makefile";
    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
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

    meta = with pkgs.stdenv.lib; {
      homepage = http://plv.csail.mit.edu/fiat/;
      description = "A library for the Coq proof assistant for synthesizing efficient correct-by-construction programs from declarative specifications";
      maintainers = with maintainers; [ jwiegley ];
      platforms = coq.meta.platforms;
    };

    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" ];
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
