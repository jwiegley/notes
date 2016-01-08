ghc7102Env = pkgs.myEnvFun {
  name = "ghc7102";
  buildInputs = with haskell7102Packages; [
    (haskell7102Packages.ghcWithPackages my-packages-7102)
    (hoogle-local my-packages-7102 haskell7102Packages)

    alex happy
    cabal-install
    ghc-core
    ghc-mod
    # hdevtools
    hlint
    simple-mirror
    hasktags
    # cabal-meta
    # lambdabot djinn mueval
    pointfree
    idris
    # threadscope
    # timeplot splot
    liquidhaskell
  ];
};
