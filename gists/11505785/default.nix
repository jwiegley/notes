{ stdenv, parallel, perl, wget, ghc, hoogle, rehoo
, packages ? with stdenv.haskellPackages; [
    async_2_0_1_4
    attoparsec_0_10_4_0
    caseInsensitive_1_0_0_1
    cgi_3001_1_7_5
    fgl_5_4_2_4
    GLUT_2_4_0_0
    GLURaw_1_3_0_0
    haskellSrc_1_0_1_5
    hashable_1_2_1_0
    html_1_0_1_2
    HTTP_4000_2_8
    HUnit_1_2_5_2
    mtl_2_1_2
    network_2_4_1_2
    OpenGL_2_8_0_0
    OpenGLRaw_1_3_0_0
    parallel_3_2_0_3
    parsec_3_1_3
    QuickCheck_2_6
    random_1_0_1_1
    regexBase_0_93_2
    regexCompat_0_95_1
    regexPosix_0_95_2
    split_0_2_2
    stm_2_4_2
    syb_0_4_0
    text_0_11_3_1
    transformers_0_3_0_0
    unorderedContainers_0_2_3_0
    vector_0_10_0_1
    xhtml_3000_2_1
    zlib_0_5_4_1
    cabalInstall_1_16_0_2
    alex_3_0_5
    haddock_2_13_2
    happy_1_18_10
    primitive_0_5_0_1
  ]
}:

stdenv.mkDerivation rec {
  name = "local-hoogle-1.0";

  src = ./.;

  buildInputs = [ parallel perl wget ghc hoogle rehoo ] ++ packages;

  installPhase = ''
    if [ -z "$packages" ]; then
        echo "ERROR: The packages attribute has not been set"
        exit 1
    fi

    HDIR=$out/share/hoogle
    
    mkdir -p $HDIR/doc
    cd $HDIR
    
    export HOOGLE_DOC_PATH=$out/share/hoogle/doc

    function import_dbs() {
        find $1 -name '*.txt' \
            | parallel -j$NIX_BUILD_CORES 'cp -p {} .; perl -i -pe "print \"\@url file://{//}/index.html\n\" if /^\@version/;" {/}; hoogle convert {/}'
    }
    
    for i in $packages; do
        import_dbs $i/share/doc
        ln -sf $i/share/doc/* $out/share/hoogle/doc
    done
    
    ln -sf ${ghc}/share/doc/ghc*/html/libraries/* $out/share/hoogle/doc

    chmod 644 *.hoo *.txt
    hoogle data -d $HDIR --redownload -l $(echo *.txt | sed 's/\.txt//g')
    rehoo -j4 -c64 .

    rm -fr downloads *.txt *.dep
    mv default.hoo x
    rm -f *.hoo
    mv x default.hoo

    mkdir -p $out/bin
    h=$out/bin/hoogle
    echo "#!/bin/bash" > $h
    echo "cmd=\$1" >> $h
    echo "shift 1" >> $h
    echo "export HOOGLE_DOC_PATH=$out/share/hoogle/doc" >> $h
    echo "${hoogle}/bin/hoogle \$cmd -d $out/share/hoogle \"\$@\"" >> $h
    chmod 755 $h
  '';

  meta = {
    homepage = "https://github.com/jwiegley/local-hoogle";
    description = "An expression for installing a fully local Hoogle with documentation and source links";
    license = stdenv.lib.licenses.bsd3;
  };
}
