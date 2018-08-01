{ compiler    ? "ghc843"
, rev         ? "49bdae006e66e70ad3245a463edc01b5749250d3"
, sha256      ? "1ijsifmap47nfzg0spny94lmj66y3x3x8i6vs471bnjamka3dx8p"
, pkgs        ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
, returnShellEnv ? pkgs.lib.inNixShell
, mkDerivation ? null
}:

with pkgs; let
  rootName = name: builtins.elemAt (lib.splitString "/" name) 0;
  isValidFile = name: files: builtins.elem (rootName name) files;
  relative = path: name: lib.removePrefix (toString path + "/") name;
  onlyFiles = files: path: builtins.filterSource (name: type: isValidFile (relative path name) files) path;

  rewriteRelative = top: path:
    let path' = lib.removePrefix top (builtins.toString path);
    in if lib.isStorePath path' then path' else ./eta + path';

  eta-nix = fetchTarball "https://github.com/eta-lang/eta-nix/archive/1638c3f133a3931ec70bd0d4f579b67fd62897e2.tar.gz";

  overrides = self: super: {
    mkDerivation = args: super.mkDerivation (lib.overrideExisting args {
      src = rewriteRelative eta-nix args.src;
    });

    eta = haskell.lib.overrideCabal super.eta (drv: {
      # Makes the build a bit faster
      src = onlyFiles ["compiler" "include" "eta" "eta.cabal" "LICENSE" "tests"] drv.src;
    });
  };

  haskellPackages = (import eta-nix { }).override { inherit overrides; };

in haskellPackages.developPackage {
  root = ./.;

  overrides = self: super: with pkgs.haskell.lib; {
  };

  source-overrides = {
  };

  modifier = drv: pkgs.haskell.lib.overrideCabal drv (attrs: {
    buildTools = with haskellPackages; [ eta etlas ];

    configurePhase = "";
    buildPhase = ''
      etlas build
      cp -pR <somewhere> $out/...
    '';
  });

  inherit returnShellEnv;
}
