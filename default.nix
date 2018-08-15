let
haskellPackages = pkgs.haskell.packages.${compiler};

sourcePackage = name: src:
  haskellPackages.callPackage ((haskellPackages.haskellSrc2nix {
    inherit name src;
  }).overrideAttrs (attrs: { src = builtins.dirOf src; }));

# dfinity-radix-tree = haskellPackages.callHackage "dfinity-radix-tree" "0.3.1" {};
dfinity-radix-tree =
  sourcePackage "dfinity-radix-tree" ../hs-radix-tree/dfinity-radix-tree.cabal {};

dfinity-common =
  sourcePackage "dfinity-common" ../hs-dfinity-common/dfinity-common.cabal {};
