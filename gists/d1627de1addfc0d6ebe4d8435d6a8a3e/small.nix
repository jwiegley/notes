with (let
  __cur_file = /Users/johnw/Downloads/nixpkgs-python/default.nix;
in { interpreter ? null
   , pkgs ? import <nixpkgs> {
     overlays = [
       (self:
         super:
           let
             inherit (self) pythonng;
           in {
             pythonng.interpreter.cpython27 = pythonng.packages.cpython27.python;
             pythonng.interpreter.cpython36 = null;
             pythonng.packages.cpython27 = null;
             pythonng.packages.cpython36 = null;
             pythonng.index = null;
           })
     ];
   } }:
  {
    inherit (null) pythonng;
  } // pkgs.pythonng.packages."") {};
[
  null
] ++ map null (cffi.pythonDepends)