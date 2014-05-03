{ stdenv
, parallel
, perl
, haskellPackages
}:

stdenv.mkDerivation {
  name = "local-hoogle-1.0";

  src = ./.;

  buildInputs = [
    parallel
    perl
  ] ++ (with haskellPackages; [
    hoogleFork
    rehoo

    haskellPlatform_2013_2_0_0
    Boolean
    #CCdelcont
    adjunctions
    aeson
    arithmoi
    attempt
    base16Bytestring
    bifunctors
    bindingsDSL
    #categories
    classyPrelude
    classyPreludeConduit
    comonad
    comonadTransformers
    #compdata
    #composition
    #cond
    conduit
    conduitCombinators
    conduitExtra
    configurator
    convertible
    cpphs
    #directory
    distributive
    doctest
    #doctestProp
    either
    ekg
    esqueleto
    exceptions
    filepath
    free
    hlint
    hspec
    hspecExpectations
    httpClient
    httpClientTls
    #kanExtensions
    keys
    lens
    liftedAsync
    liftedBase
    linear
    listExtras
    monadControl
    #monadCoroutine
    monadLogger
    monadLoops
    monadPar
    monadParExtras
    #monadStm
    monadloc
    monoidExtras
    #multimap
    newtype
    numbers
    operational
    optparseApplicative
    persistent
    persistentPostgresql
    persistentSqlite
    persistentTemplate
    pointed
    posixPaths
    prettyShow
    process
    #profunctorExtras
    profunctors
    #recursionSchemes
    reducers
    reflection
    #regexApplicative
    resourcePool
    resourcet
    retry
    #rex
    safe
    semigroupoids
    semigroups
    shake
    shakespeareText
    shelly
    simpleReflect
    #snappy
    #speculation
    spoon
    stmChans
    stmConduit
    #stmStats
    strict
    stringsearch
    systemFileio
    systemFilepath
    tagged
    tar
    temporary
    these
    thyme
    #timers
    void
    wai
    warp
    xmlLens
    yesod
  ]);

  buildPhase = ''
    HDIR=$out/share/hoogle
    
    test -d $HDIR || mkdir -p $HDIR
    cd $HDIR
    
    function import_dbs() {
        find $1 -name '*.txt' \
            | parallel 'cp -p {} .; perl -i -pe "print \"\@url file://{//}/index.html\n\" if /^\@version/;" {/}; hoogle convert {/}'
    }
    
    for i in "$buildDepends"; do
        echo $i/share/doc
        import_dbs $i/share/doc
    done
    
    hoogle data -d $HDIR --redownload -l $(echo *.txt | sed 's/\.txt//g')
    rehoo -j4 -c64 .
  '';

  meta = {
    homepage = "https://github.com/jwiegley/haskell-deps";
    description = "My extended version of the Haskell Platform";
    license = stdenv.lib.licenses.bsd3;
  };
}
