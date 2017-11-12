{ stdenv, fetchgit, coq, ocamlPackages, which, unzip
, tools ? stdenv.cc
}:

stdenv.mkDerivation rec {
  name = "vst-${coq.coq-version}-20170715";

  src = fetchgit {
    url = "https://github.com/PrincetonUniversity/VST.git";
    rev = "666b67de61b7494bb58758edc409701859bfb31c";
    sha256 = "19yfk7p9r5vjfmsia6lsmfzjblai5w9yy7vncj5w7aczchscs743";
  };

  src2 = fetchgit {
    url = "https://github.com/ildyria/CompCert.git";
    rev = "2e2a2663c47d0bd1ae3279bc253662d69dcaf483";
    sha256 = "07nalmydci0wj2x3s3crfylz94zbj52dz5zz188ypd7mjy2m1sw1";
  };

  buildInputs = [ coq.ocaml coq.camlp5 which unzip ]
    ++ (with ocamlPackages; [ findlib menhir ]);
  propagatedBuildInputs = [ coq ];

  enableParallelBuilding = true;

  configurePhase = ''
    cp -pR ${src2} compcert
    cd compcert
    substituteInPlace ./configure --replace '{toolprefix}gcc' '{toolprefix}cc'
    ./configure -clightgen -prefix $out -toolprefix ${tools}/bin/ '' +
    (if stdenv.isDarwin then "ia32-macosx" else "ia32-linux") + ''
    cd ..
  '';

  buildPhase = ''
    (cd compcert; make)
    COMPCERT=compcert > CONFIGURE
    make
  '';

  meta = with stdenv.lib; {
    homepage = https://github.com/PrincetonUniversity/VST;
    license = licenses.bsd3;
    maintainers = [ maintainers.jwiegley ];
    platforms = coq.meta.platforms;
  };

}
