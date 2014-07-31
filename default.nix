    lens          = disableTest (pkgs.recurseIntoAttrs ((callPackage ./nix/lens-3.10.2.nix {}).override {
      contravariant = callPackage ./nix/contravariant-0.6.1.1.nix {};
    }));
