{
  description = "Coq/Rocq notes and experiments";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    category-theory.url = "path:/Users/johnw/src/category-theory";
  };

  outputs = { self, nixpkgs, flake-utils, category-theory }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        catPkgs = category-theory.packages.${system};
      in {
        devShells = rec {
          coq-notes = coqPackages:
            let
              coq = pkgs.${coqPackages}.coq;
              isRocq = coqPackages == "coqPackages_9_0" || coqPackages == "coqPackages_9_1";
              rocqPackages = if coqPackages == "coqPackages_9_0" then "rocqPackages_9_0"
                             else if coqPackages == "coqPackages_9_1" then "rocqPackages_9_1"
                             else null;
              stdlib = if rocqPackages != null then pkgs.${rocqPackages}.stdlib else null;

              catthy = catPkgs.${"category-theory_" +
                (if coqPackages == "coqPackages_9_1" then "9_1"
                 else if coqPackages == "coqPackages_9_0" then "9_0"
                 else if coqPackages == "coqPackages_8_20" then "8_20"
                 else if coqPackages == "coqPackages_8_19" then "8_19"
                 else "9_1")};
            in pkgs.mkShell {
              name = "coq-notes-shell";

              buildInputs = [
                coq coq.ocaml coq.findlib catthy
              ] ++ pkgs.lib.optionals (stdlib != null) [
                stdlib
              ];

              ROCQPATH = if isRocq then "${catthy}/lib/coq/${coq.coq-version}/user-contrib" else null;
              COQPATH = if isRocq then null else "${catthy}/lib/coq/${coq.coq-version}/user-contrib";

              shellHook = ''
                echo "Coq/Rocq ${coq.coq-version} development environment"
                echo "Available: coqc, coqtop, coq_makefile"
                echo "Libraries: Category (includes Equations)"
              '';
            };

          coq-notes_8_19 = coq-notes "coqPackages_8_19";
          coq-notes_8_20 = coq-notes "coqPackages_8_20";
          coq-notes_9_0 = coq-notes "coqPackages_9_0";
          coq-notes_9_1 = coq-notes "coqPackages_9_1";

          default = coq-notes_9_1;
        };
      });
}
