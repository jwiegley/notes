{ cabal, conduit, conduitCombinators, attoparsec, systemFilepath
, unixCompat, text, regexPosix, profunctors, hspec, time
, semigroups, exceptions
}:

cabal.mkDerivation (self: {
  pname = "find-conduit";
  version = "0.2.3";
  src = ./.;
  buildDepends = [
    conduit conduitCombinators attoparsec systemFilepath text
    unixCompat regexPosix profunctors hspec time semigroups
    exceptions
  ];
  meta = {
    homepage = "https://github.com/yesodweb/Shelly.hs";
    description = "shell-like (systems) programming in Haskell";
    license = self.stdenv.lib.licenses.bsd3;
    platforms = self.ghc.meta.platforms;
    maintainers = [ self.stdenv.lib.maintainers.andres ];
  };
})
