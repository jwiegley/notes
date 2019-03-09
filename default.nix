{ version  ? "0.0"
, hostname ? "vulcan"
}:

let
  localconfig = "./config/${hostname}.nix";

  extendNixPath = paths:
    let
      overrides = {
        nixPath = paths ++ builtins.nixPath;
        import = fn: scopedImport overrides fn;
        scopedImport = attrs: fn: scopedImport (overrides // attrs) fn;
        builtins = builtins // overrides;
      };

    in scopedImport overrides;

  locallyImport = extendNixPath
    [{ prefix = "localconfig";
       path = localconfig; }];

  darwin = locallyImport <darwin> {};

  home-manager = locallyImport ./home-manager/home-manager/home-manager.nix {
    confPath = ./config/home.nix;
    confAttr = "";
  };

in darwin.pkgs.buildEnv rec {
  name = "nix-config-${version}";
  paths = [
    darwin.system
    home-manager.activationPackage
    darwin.pkgs.allEnvs
  ];
}
