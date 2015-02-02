{ packageOverrides = pkgs: rec {

# emacs = pkgs.emacs24Macport;

ledger = pkgs.callPackage /Users/johnw/Projects/ledger {};

findConduitEnv = pkgs.myEnvFun {
  name = "findConduit";
  buildInputs = 
       haskellPackages_ghc782.findConduit.propagatedUserEnvPkgs
    ++ ghcEnv_782.nativeBuildInputs
    ;
};

buildToolsEnv = pkgs.buildEnv {
  name = "buildTools";
  paths = with pkgs; [
    cmake ninja gnumake automake autoconf
  ];
};

emailToolsEnv = pkgs.buildEnv {
  name = "emailTools";
  paths = with pkgs; [
    leafnode dovecot22 dovecot_pigeonhole fetchmail procmail w3m
  ];
};

haskellPackages_ghc782 =
  let callPackage = pkgs.lib.callPackageWith haskellPackages_ghc782;
  in pkgs.recurseIntoAttrs (pkgs.haskellPackages_ghc782.override {
      extraPrefs = self: {
        gitAll          = callPackage /Users/johnw/Projects/git-all {};
        hours           = callPackage /Users/johnw/Projects/hours {};
        loggingHEAD     = callPackage /Users/johnw/Projects/logging {};
        pushme          = callPackage /Users/johnw/Projects/pushme {};
        simpleMirror    = callPackage /Users/johnw/Projects/simple-mirror {};

        shelly          = callPackage /Users/johnw/src/shelly {};
        shellyExtra     = callPackage /Users/johnw/src/shelly/shelly-extra {};
        lensHEAD        = callPackage /Users/johnw/src/lens {};

        newartisans     = callPackage /Users/johnw/src/newartisans {};

        gitlib          = callPackage /Users/johnw/Projects/gitlib/gitlib {};
        gitlibTest      = callPackage /Users/johnw/Projects/gitlib/gitlib-test {};
        hlibgit2        = callPackage /Users/johnw/Projects/gitlib/hlibgit2 {};
        gitlibLibgit2   = callPackage /Users/johnw/Projects/gitlib/gitlib-libgit2 {};
        gitMonitor      = callPackage /Users/johnw/Projects/gitlib/git-monitor {};

        bugs            = callPackage /Users/johnw/Projects/bugs {};
        findConduit     = callPackage /Users/johnw/Projects/find-conduit {};
        tryhaskell      = callPackage /Users/johnw/Projects/tryhaskell {};
        consistent      = callPackage /Users/johnw/Projects/consistent {};
        theseHEAD       = callPackage /Users/johnw/Projects/these {};

        # The nixpkgs expression is too out-of-date to build with 7.8.2.
        hdevtools       = callPackage /Users/johnw/Projects/hdevtools {};

        conduitHEAD            = callPackage /Users/johnw/Projects/conduit/conduit {};
        conduitCombinatorsHEAD = callPackage /Users/johnw/Projects/conduit-combinators {};

        codex = callPackage /Users/johnw/Projects/nixpkgs/pkgs/development/tools/haskell/codex {};
      };
    });

# These are packages which only work with the currently standard GHC, and so
# need to be overridden there.
haskellPackages =
  let callPackage = pkgs.lib.callPackageWith haskellPackages;
  in pkgs.recurseIntoAttrs (pkgs.haskellPackages.override {
      extraPrefs = self: {
        ghcMod = pkgs.haskellPackages.ghcMod.override {
          # emacs = pkgs.emacs24Macport;
        };
        hoogleFork = callPackage /Users/johnw/src/hoogle {};
      };
    });

ghc = pkgs.ghc // {
  ghcHEAD = pkgs.callPackage /Users/johnw/Projects/ghc {};
};

hoogleLocal_ghc782 = pkgs.callPackage /Users/johnw/src/hoogle-local {
  ghc      = ghc.ghc782;
  hoogle   = haskellPackages.hoogleFork;
  rehoo    = haskellPackages_ghc782.rehoo;
  packages = myPackages;
};

ghcEnv_782 = pkgs.myEnvFun {
    name = "ghc782";
    buildInputs = with pkgs; [ 
      stdenv
      ghc.ghc782
      hoogleLocal_ghc782
    ] ++ myPackages
      ++ (with haskellPackages_ghc782; [
      #cabalBounds
      cabalInstall_1_20_0_0
      #codex
      ghcCore
      ghcMod
      hdevtools
      hlint
    ]) ++ (with haskellPackages; [
      Agda
      AgdaStdlib
      cabal2nix
      hasktags
      #hsenv
      lambdabot
      #threadscope
    ]) ++ (with haskellPackages_ghc782;
      pkgs.stdenv.lib.concatMap (self: self.propagatedUserEnvPkgs) [
        gitAll
        hours
        loggingHEAD
        pushme
        simpleMirror
        
        shelly
        #shellyExtra
        lensHEAD
        
        newartisans
        
        #gitlib
        #gitlibTest
        #hlibgit2
        #gitlibLibgit2
        #gitMonitor
        
        bugs
        findConduit
        tryhaskell
        consistent
        theseHEAD
        
        hdevtools
        
        conduitHEAD
        conduitCombinatorsHEAD
      ]);
};

ghcEnv_HEAD = pkgs.myEnvFun {
    name = "ghcHEAD";
    buildInputs = with pkgs; [ 
        stdenv
        ghc.ghcHEAD
    ] ++ (with pkgs.haskellPackages; [
        cabalInstall_1_20_0_0
        ghcMod
        hasktags
        hdevtools
        cabal2nix
    ]);
};

hoogleLocal_ghc763 = pkgs.callPackage /Users/johnw/src/hoogle-local  {
  ghc      = ghc.ghc763;
  hoogle   = haskellPackages.hoogleFork;
  rehoo    = haskellPackages.rehoo;
  packages = myPackages;
};

ghcEnv_763 = pkgs.myEnvFun {
    name = "ghc763";
    buildInputs = with pkgs; [ 
        stdenv
        ghc.ghc763
        hoogleLocal_ghc763
    ] ++ (with pkgs.haskellPackages_ghc763; [
        cabalInstall_1_18_0_3
        #cabalBounds
        hlint
        #threadscope
        ghcCore
        ghcMod
        hasktags
        hdevtools
        cabal2nix
        lambdabot
    ]);
};

myPackages = with haskellPackages_ghc782; [
  Boolean
  CCdelcont
  Crypto
  DAV
  HTTP
  HUnit
  IfElse
  MemoTrie
  MissingH
  MonadCatchIOTransformers
  QuickCheck
  abstractDeque
  abstractPar
  adjunctions
  aeson
  annotatedWlPprint
  ansiTerminal
  ansiWlPprint
  appar
  arithmoi
  asn1Encoding
  asn1Parse
  asn1Types
  async
  attempt
  attoparsec
  attoparsecConduit
  attoparsecEnumerator
  authenticate
  base16Bytestring
  base64Bytestring
  baseUnicodeSymbols
  basicPrelude
  bifunctors
  bindingsDSL
  blazeBuilder
  blazeBuilderConduit
  blazeBuilderEnumerator
  blazeHtml
  blazeMarkup
  blazeTextual
  byteable
  byteorder
  bytestringMmap
  caseInsensitive
  #categories
  cereal
  cerealConduit
  charset
  cheapskate
  chunkedData
  cipherAes
  cipherRc4
  classyPrelude
  classyPreludeConduit
  clientsession
  cmdargs
  comonad
  comonadTransformers
  #compdata
  composition
  cond
  conduit
  conduitCombinators
  conduitExtra
  configurator
  connection
  contravariant
  convertible
  cookie
  cpphs
  cprngAes
  cryptoApi
  cryptoCipherTypes
  cryptoNumbers
  cryptoPubkey
  cryptoPubkeyTypes
  cryptoRandom
  cryptohash
  cryptohashConduit
  cssText
  dataDefault
  dataDefaultClass
  dataDefaultInstancesBase
  dataDefaultInstancesContainers
  dataDefaultInstancesDlist
  dataDefaultInstancesOldLocale
  dataenc
  derive
  distributive
  dlist
  dlistInstances
  dns
  doctest
  doctestProp
  editDistance
  either
  #ekg
  emailValidate
  enclosedExceptions
  entropy
  enumerator
  errors
  esqueleto
  exceptions
  extensibleExceptions
  failure
  fastLogger
  feed
  fgl
  fileEmbed
  filepath
  fingertree
  free
  #geniplate
  ghcPaths
  gnuidn
  gnutls
  groups
  gsasl
  hamlet
  hashable
  hashtables
  haskeline
  haskellLexer
  haskellSrc
  haskellSrcExts
  haskellSrcMeta
  hfsevents
  hjsmin
  hlint
  hoogle
  hscolour
  hslogger
  hspec
  hspecExpectations
  html
  httpClient
  httpClientTls
  httpConduit
  httpDate
  httpTypes
  hxt
  hxtCharproperties
  hxtRegexXmlschema
  hxtUnicode
  iproute
  json
  kanExtensions
  keys
  languageJava
  languageJavascript
  lens
  libxmlSax
  liftedAsync
  liftedBase
  linear
  listExtras
  mimeMail
  mimeTypes
  mmorph
  monadControl
  monadCoroutine
  monadLogger
  monadLoops
  monadPar
  monadParExtras
  monadStm
  monadloc
  monoidExtras
  mtl
  multimap
  network
  newtype
  numbers
  operational
  optparseApplicative
  parallel
  parallelIo
  parsec
  persistent
  persistentPostgresql
  persistentSqlite
  persistentTemplate
  pointed
  posixPaths
  prettyShow
  profunctors
  random
  #recursionSchemes
  reducers
  reflection
  regexApplicative
  regexBase
  regexCompat
  regexPosix
  resourcePool
  resourcet
  retry
  rex
  safe
  semigroupoids
  semigroups
  shake
  shakespeare
  shelly
  simpleReflect
  speculation
  split
  spoon
  stm
  stmChans
  stmConduit
  stmStats
  strict
  stringsearch
  systemFileio
  systemFilepath
  tagged
  tar
  temporary
  text
  these
  thyme
  time
  transformers
  transformersBase
  unixCompat
  unorderedContainers
  vector
  void
  wai
  warp
  xhtml
  xmlLens
  zlib
];

}; }
