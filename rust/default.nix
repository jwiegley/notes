{ rev    ? "a3a23d9599b0a82e333ad91db2cdc479313ce154"
, sha256 ? "05xmgrrnw6j39lh3d48kg064z510i0w5vvrm1s5cdwhdc2fkspjq"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
, returnShellEnv ? pkgs.lib.inNixShell
, mkDerivation ? null
}:

with pkgs; rustPlatform.buildRustPackage rec {
  pname = "hello";
  version = "1.0.0";

  src = ./.;

  cargoSha256 = "02ix7i6i98mg8rz5qcqcgpm9bqbwvy53n5w8ji0ldg7civkvlfrx";

  cargoBuildFlags = [];

  nativeBuildInputs = [
    asciidoc asciidoctor plantuml docbook_xsl libxslt rls rustfmt clippy
  ];
  buildInputs = [ ]
    ++ (lib.optional stdenv.isDarwin darwin.apple_sdk.frameworks.Security);

  preFixup = ''
  '';

  meta = with lib; {
    description = "Hello, world!";
    homepage = https://github.com/jwiegley/hello;
    license = with licenses; [ mit ];
    maintainers = [ maintainers.jwiegley ];
    platforms = platforms.all;
  };
}
