  ListMoreUtilsXS = buildPerlPackage rec {
     name = "List-MoreUtils-XS-0.428";
     src = fetchurl {
       url = mirror://cpan/authors/id/R/RE/REHSACK/List-MoreUtils-XS-0.428.tar.gz;
       sha256 = "0bfndmnkqaaf3gffprak143bzplxd69c368jxgr7rzlx88hyd7wx";
     };
     propagatedBuildInputs = [ XSLoader ];
     preConfigure = stdenv.lib.optionalString stdenv.isDarwin ''
       export LD=$CC
     '';
     meta = {
       description = "Provide the stuff missing in List::Util in XS";
       license = with stdenv.lib.licenses; [ asl20 ];
       homepage = "https://metacpan.org/release/List-MoreUtils-XS";
     };
  };
