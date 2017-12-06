ocaml-ng = super.stdenv.lib.overrideDerivation super.ocaml-ng (attrs: {
  ocamlPackages_4_06 = 
      super.stdenv.lib.overrideDerivation attrs.ocamlPackages_4_06 (attrs: {
    ppx_core = super.stdenv.lib.overrideDerivation attrs.ppx_core (attrs: {
      src = super.fetchFromGithub {
        owner = "janestreet";
        repo = "ppx_core";
        rev = "c21c37ad54becee48f1bd747eab56620e858f3b7";
        sha256 = "0xwnyw45zxlkndp29ngi0fmvsskl7q99fmmv8g4cy1plsk5yrvix";
      };
    });
  });
});
