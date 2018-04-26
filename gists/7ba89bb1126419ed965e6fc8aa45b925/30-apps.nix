Docker = self.installApplication rec {
  name = "Docker";
  version = "17.12.0-ce-mac49";
  sourceRoot = "Docker.app";
  src = super.fetchurl {
    url = https://download.docker.com/mac/stable/Docker.dmg;
    sha256 = "0dvr3mlvrwfc9ab6dyx351vraqx01lzxgz8vrczs0vhm2rpv3kdy";
    # date = 2018-02-04T16:36:09-0800;
  };
  description = ''
    Docker CE for Mac is an easy-to-install desktop app for building,
    debugging, and testing Dockerized apps on a Mac
  '';
  homepage = https://store.docker.com/editions/community/docker-ce-desktop-mac;
};
