{ packages ? "agdaPackages"
, rev      ? "8e1891d5b8d0b898db8890ddab73141f0cd3c2bc"
, sha256   ? "0a767mn0nfp4qnklsvs6bnc0vng4nc3ch566nmrz18ypk67z4zz0"
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
  name = "plfa-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [
    (agda.withPackages (p: [p.standard-library p.agda-categories]))
    pkgs.git
    pkgs.haskellPackages.pandoc
  ];

  phases = [ "unpackPhase" "patchPhase" "buildPhase" ];

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
