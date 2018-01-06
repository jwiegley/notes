  nixpkgs.config = {
    allowUnfree      = true;
    allowBroken      = true;
    packageOverrides = pkgs: import ./overrides.nix { pkgs = pkgs; };
  };

  nixpkgs.overlays = 
    let path = ./overlays; in with builtins;
    map (n: import (path + ("/" + n)))
        (filter (n: match ".*\\.nix" n != null || 
                    pathExists (path + ("/" + n + "/default.nix")))
                (attrNames (readDir path)));
