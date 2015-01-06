haskellPackages_ghcHEAD = haskell.packages_ghcHEAD.noProfiling;
haskellPackages_ghcHEAD_profiling = haskell.packages_ghcHEAD.profiling;

ghcEnv_HEAD = pkgs.myEnvFun {
  name = "ghcHEAD";
  buildInputs = with haskellPackages_ghcHEAD; [
    pkgs.ghc.ghcHEAD cabalInstall_1_20_0_3
  ];
};
