  buildPhase = ''
    ensureDir $out/Applications
    cp -pR build/Foo.app $out/Applications
  '';