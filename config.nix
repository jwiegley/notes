{ pkgs }: {

packageOverrides = super: let self = super.pkgs; in with self; rec {

nix = self.nix.overrideDerivation { 
  src = self.fetchgit {
    url = git://github.com/NixOS/nix.git;
    rev = "d1e3bf01bce7d8502610532077f6f55c3df4de2c";
    sha256 = "fde3730455c3c91b2fd612871fa7262bdacd3dff4ba77c5dfbc3c1f0de9b8a36";
  };
};
