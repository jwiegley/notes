let inherit ((import <darwin> {}).pkgs)
      lib nixBufferBuilders
      coq_8_7 coqPackages_8_7;

      coq         = coq_8_7;
      coqPackages = coqPackages_8_7;

in nixBufferBuilders.withPackages [
  coq coqPackages.equations coqPackages.fiat_HEAD coqPackages.coq-haskell
]
