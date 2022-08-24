{ pkgs ? (import <darwin> {}).pkgs }:

pkgs.stdenv.mkDerivation rec {
  name = "notes-acl2-${version}";
  version = "1.0";

  src = ./.;

  buildInputs = with pkgs; [ acl2 ];
  enableParallelBuilding = true;

  buildPhase = "echo yes";
  installFlags = "mkdir -p $out";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
}
