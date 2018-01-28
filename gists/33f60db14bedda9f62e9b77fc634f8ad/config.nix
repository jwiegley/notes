coq-serapi = callPackage ~/oss/coq-serapi {
  coq = coq_8_7;
  ocamlPackages = ocamlPackages_4_04;
};

ocamlPackages_4_04 = 
  super.ocaml-ng.ocamlPackages_4_04 // { ppx_deriving = ppx_deriving; };

ppx_deriving = super.stdenv.lib.overrideDerivation
  super.ocaml-ng.ocamlPackages_4_04.ppx_deriving (attrs: {
  name = "ocaml-ppx_deriving-4.1";
  version = "4.1";
  src = super.fetchFromGitHub {
    owner  = "ocaml-ppx";
    repo   = "ppx_deriving";
    rev    = "v4.1";
    sha256 = "0cy9p8d8cbcxvqyyv8fz2z9ypi121zrgaamdlp4ld9f3jnwz7my9";
  };
});
