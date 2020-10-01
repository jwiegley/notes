{ packages ? "agdaPackages"
, rev      ? "502845c3e31ef3de0e424f3fcb09217df2ce6df6"
, sha256   ? "0fcqpsy6y7dgn0y0wgpa56gsg0b0p8avlpjrd79fp4mp9bl18nda"
, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/jwiegley/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
    overlays = [];
  }
}:

with pkgs.${packages};

pkgs.stdenv.mkDerivation rec {
  name = "cat-linear-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [
    (agda.withPackages (p: [p.standard-library p.agda-categories]))
  ];

  buildPhase = ''
    cd src
    for i in *.agda; do
        agda --compile $i
    done
  '';

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
