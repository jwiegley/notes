{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, aeson, base, c2hsc, containers, directory
      , filepath, hspec, language-c, lens, mtl, optparse-applicative
      , process, QuickCheck, split, stdenv, temporary, transformers, yaml
      , parsec, unordered-containers
      }:
      mkDerivation {
        pname = "z3";
        version = "4.5.0";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [ base containers mtl ];
        librarySystemDepends = [ pkgs.z3 ];
        executableHaskellDepends = [
          aeson base c2hsc containers directory filepath language-c lens mtl
          optparse-applicative process split temporary transformers yaml
          parsec unordered-containers
        ];
        testHaskellDepends = [ base hspec QuickCheck ];
        homepage = "http://bitbucket.org/iago/z3-haskell";
        description = "Bindings for the Z3 Theorem Prover";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
