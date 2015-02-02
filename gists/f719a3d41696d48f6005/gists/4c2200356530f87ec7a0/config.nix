clangEnv = pkgs.myEnvFun {
    name = "clang";
    buildInputs = [ clang llvm ];
  };
