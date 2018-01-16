let pkgs = import <nixpkgs> {}; in

pkgs.buildEnv {
  name = "emacsWithPackages-org-bug";
  paths = [
   ((pkgs.emacsPackagesNg.overrideScope (super: self: {
      org = pkgs.stdenv.lib.overrideDerivation super.org (attrs: rec {
        name = "emacs-org-${version}";
        version = "20160421";
        src = pkgs.fetchFromGitHub {
          owner  = "jwiegley";
          repo   = "org-mode";
          rev    = "db5257389231bd49e92e2bc66713ac71b0435eec";
          sha256 = "073cmwgxga14r4ykbgp8w0gjp1wqajmlk6qv9qfnrafgpxic366m";
        };
      });
      })).emacsWithPackages (epkgs: with epkgs; [ org ])) ];
}

# Then run:
#
# ls -d $(cat ./result/bin/emacs | grep site-lisp | sed "s|.*}'/nix|/nix|" | sed "s|:'||")/elpa/org-20*
