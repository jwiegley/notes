    lens          = disableTest (callPackage ./nix/lens-3.10.2.nix {
      contravariant = callPackage ./nix/contravariant-0.6.1.1.nix {};
      comonad       = pkgs.haskellPackages.comonad.override {
        contravariant = callPackage ./nix/contravariant-0.6.1.1.nix {};
      };
      semigroupoids = pkgs.haskellPackages.semigroupoids.override {
        contravariant = callPackage ./nix/contravariant-0.6.1.1.nix {};
        comonad       = pkgs.haskellPackages.comonad.override {
          contravariant = callPackage ./nix/contravariant-0.6.1.1.nix {};
        };
      };
    });
