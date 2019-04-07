  NetSSLeay = buildPerlPackage rec {
    name = "Net-SSLeay-1.85";
    src = fetchurl {
      url = "mirror://cpan/authors/id/M/MI/MIKEM/${name}.tar.gz";
      sha256 = "1j5h4ycm8538397l204d2d5fkm9595aj174pj7bkpbhwzfwqi0cx";
    };
    buildInputs = [ pkgs.openssl ];
    doCheck = false; # Test performs network access.
    preConfigure = ''
      mkdir openssl
      ln -s ${pkgs.openssl.out}/lib openssl
      ln -s ${pkgs.openssl.bin}/bin openssl
      ln -s ${pkgs.openssl.dev}/include openssl
      export OPENSSL_PREFIX=$(realpath openssl)
    '';
    meta = {
      description = "Perl extension for using OpenSSL";
      license = stdenv.lib.licenses.artistic2;
    };
  };
