    structuredHaskellMode = callPackage ../applications/editors/emacs-modes/structured-haskell-mode {
      inherit (haskellPackages) cabal haskellSrcExts;
    };
