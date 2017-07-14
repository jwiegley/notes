coq86Env = pkgs.myEnvFun {
  name = "coq86";
  buildInputs = [
    ocaml ocamlPackages.camlp5_transitional
    coq_8_6
    coqPackages_8_6.dpdgraph
    coqPackages_8_6.flocq
    coqPackages_8_6.mathcomp
    coqPackages_8_6.ssreflect
    coqPackages_8_6.QuickChick
    coqPackages_8_6.coq-ext-lib
    coqPackages_8_6.coquelicot
    compcert
  ];
};
