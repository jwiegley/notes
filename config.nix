emacsToolsEnv = pkgs.buildEnv {
  name = "emacsTools";
  paths = with emacsPackagesNgGen emacs; [
    emacs
    aspell
    aspellDicts.en
    pkgs.auctex
    emacs24Packages.proofgeneral
  ];
};
