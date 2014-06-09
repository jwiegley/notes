  postInstall = ''
    mv $out/bin/yesod $out/bin/.yesod-wrapped
    cat - > $out/bin/yesod <<EOF
    #! ${self.stdenv.shell}
    export HSENV=1
    export PACKAGE_DB_FOR_GHC='$( ${self.ghc.GHCGetPackages} ${self.ghc.version} | tr " " "\n" | tail -n +2 | paste -d " " - - | sed 's/.*/-g "&"/' | tr "\n" " ")'
    eval exec $out/bin/.yesod-wrapped "\$@"
    EOF
    chmod +x $out/bin/yesod
  '';
