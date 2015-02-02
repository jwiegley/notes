  emacs24Macport = callPackage ../applications/editors/emacs-24/macport.nix {
    # use clangStdenv on darwin to deal with: unexec: 'my_edata is not in
    # section __data'
    stdenv = if stdenv.isDarwin
      then clangStdenv
      else stdenv;
  };
