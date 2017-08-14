{ nixpkgs ? import <nixpkgs> {}, compiler ? "default" }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, active, aeson, base, colour, containers
      , data-default, diagrams, diagrams-lib, diagrams-svg, directory
      , fgl, freer-effects, graphviz, here, lens, lens-aeson, mtl
      , optparse-applicative, scientific, silently, split, stdenv, stm
      , text, time, transformers, vector, yaml, z3
      }:
      mkDerivation {
        pname = "concerto";
        version = "0.3.0";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [
          active aeson base colour containers data-default diagrams
          diagrams-lib diagrams-svg directory fgl freer-effects graphviz here
          lens lens-aeson mtl optparse-applicative scientific silently split
          stm text time transformers vector yaml z3 pkgs.darwin.apple_sdk.frameworks.Cocoa
        ];
        executableSystemDepends = [ pkgs.darwin.apple_sdk.frameworks.Cocoa ];
        executableToolDepends = [ pkgs.darwin.apple_sdk.frameworks.Cocoa ];
        executableHaskellDepends = [
          active aeson base colour containers data-default diagrams
          diagrams-lib diagrams-svg directory fgl freer-effects graphviz here
          lens lens-aeson mtl optparse-applicative scientific silently split
          stm text time transformers vector yaml z3 pkgs.darwin.apple_sdk.frameworks.Cocoa
        ];
        description = "Initial draft of CONCERTO solver";
        license = stdenv.lib.licenses.mit;
      };

  haskellPackages = if compiler == "default"
                       then haskell802Packages
                       else profiledHaskell802Packages.${compiler};

  drv = haskellPackages.callPackage f {};

in

  if pkgs.lib.inNixShell then drv.env else drv
