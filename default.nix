{ stdenv
, parallel
, perl
, wget
, ghc
, haskellPackages
}:

stdenv.mkDerivation rec {
  name = "local-hoogle-1.0";

  src = ./.;

  packages = with haskellPackages; [
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
  ];

  buildInputs = [
    parallel
    perl
    wget
  ] ++ packages;

  installPhase = ''
    HDIR=$out/share/hoogle
    
    mkdir -p $HDIR/doc
    cd $HDIR
    
    export HOOGLE_DOC_PATH=$out/share/hoogle/doc

    function import_dbs() {
        find $1 -name '*.txt' \
            | parallel 'cp -p {} .; perl -i -pe "print \"\@url file://{//}/index.html\n\" if /^\@version/;" {/}; hoogle convert {/}'
    }
    
    for i in $packages; do
        import_dbs $i/share/doc
        cp -pR $i/share/doc/* $out/share/hoogle/doc
    done
    
    cp -pR ${ghc.ghc763}/share/doc/ghc*/html/libraries/* $out/share/hoogle/doc

    chmod 644 *.hoo *.txt
    hoogle data -d $HDIR --redownload -l $(echo *.txt | sed 's/\.txt//g')
    rehoo -j4 -c64 .

    mkdir -p $out/bin
    h=$out/bin/hoogle
    echo "#!/bin/bash" > $h
    echo "cmd=\$1" >> $h
    echo "shift 1" >> $h
    echo "export HOOGLE_DOC_PATH=$out/share/hoogle/doc" >> $h
    echo "${haskellPackages.hoogleFork}/bin/hoogle \$cmd -d $out/share/hoogle \"\$@\"" >> $h
    chmod 755 $h
  '';

  meta = {
    homepage = "https://github.com/jwiegley/local-hoogle";
    description = "An expression for installing a fully local Hoogle";
    license = stdenv.lib.licenses.bsd3;
  };
}
