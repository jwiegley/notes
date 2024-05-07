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

pkgs.stdenv.mkDerivation rec {
  name = "agda-notes-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = [
    (pkgs.agdaPackages.agda.withPackages (p: [
       p.standard-library p.agda-categories
     ]))
  ];

  libraryFile = "${libraryName}.agda-lib";
  libraryName = "notes";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
