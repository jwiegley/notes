{ pkgs ? (import <darwin> {}).pkgs
, returnShellEnv ? pkgs.lib.inNixShell
, mkDerivation ? null
}:

with pkgs; rustPlatform.buildRustPackage rec {
  pname = "notes";
  version = "1.0.0";

  src = ./.;

  cargoSha256 = "sha256-Eklefz/qCfUiLU03kym3EhWd5sMb4RwyCTvHI7UoCHo=";

  cargoBuildFlags = [];

  RUSTC_BOOTSTRAP = 1;

  nativeBuildInputs = [ rust-analyzer rustfmt clippy pkg-config cargo-expand ];
  buildInputs = [ openssl protobuf ]
    ++ (lib.optional stdenv.isDarwin darwin.apple_sdk.frameworks.Security);
}
