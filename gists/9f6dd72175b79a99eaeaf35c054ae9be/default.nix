{ rev     ? "49bdae006e66e70ad3245a463edc01b5749250d3"
, sha256  ? "1ijsifmap47nfzg0spny94lmj66y3x3x8i6vs471bnjamka3dx8p"
, pkgs    ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config = {
      allowUnfree = true;
      allowBroken = false;
      allowUnsupportedSystem = true;
    };
  }
, returnShellEnv ? pkgs.lib.inNixShell
, mkDerivation ? null
}:

let
  drv = with pkgs; stdenv.mkDerivation rec {
    name = "firrtl-${version}";
    version = "0.1";
    src = ./.;
    buildInputs = [ jdk8 verilator sbt-with-scala-native ];
    env = buildEnv {
      name = name;
      paths = buildInputs;
    };
    shellHook = ''
      export PATH="$PATH:${sbt-with-scala-native}/bin"
    '';
  };

in if returnShellEnv then drv.env else drv
