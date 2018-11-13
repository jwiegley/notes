{ rev      ? "89b618771ad4b0cfdb874dee3d51eb267c4257dd"
, sha256   ? "0jlyggy7pvqj2a6iyn44r7pscz9ixjb6fn6s4ssvahfywsncza6y"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

pkgs.stdenv.mkDerivation rec {
  name = "tla-notes";
  version = "0.1";

  src =
    if pkgs.lib.inNixShell
    then null
    else if pkgs ? coqFilterSource
         then pkgs.coqFilterSource [] ./.
         else ./.;

  buildInputs = [ pkgs.tlaplus ];

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
