
  nixpkgs.config.allowUnfree = true;
  nixpkgs.config.packageOverrides = pkgs: {
    crashplan =
      let nixos-unstable =
        import /nix/var/nix/profiles/per-user/root/channels/nixos-unstable/nixpkgs {}; in
      nixos-unstable.crashplan;
  };
