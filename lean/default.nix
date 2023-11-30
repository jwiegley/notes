args@{
  rev    ? "90e85bc7c1a6fc0760a94ace129d3a1c61c3d035"
, sha256 ? "03bnmpdmh1h6pb7pfzw5w3hm6nzkg9s1kcrwgw1gmdlhivrmnx75"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

# with pkgs.${coqPackages};

pkgs.stdenv.mkDerivation rec {
  name = "lean-notes";
  version = "1.0";

  src =
    if pkgs.lib.inNixShell
    then null
    else ./.;

  buildInputs = [
    pkgs.lean4
  ];
  enableParallelBuilding = true;

  buildPhase = "make -j$NIX_BUILD_CORES";
  # preBuild = "coq_makefile -f _CoqProject -o Makefile";
  # installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    # compatibleCoqVersions = v: builtins.elem v [ "8.10" "8.11" "8.12" "8.13" ];
 };
}
