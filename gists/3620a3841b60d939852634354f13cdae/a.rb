Last login: Wed Jul  5 13:37:36 on ttys010
✔ ~/Contracts/OSS/Projects/ghc [master|✚ 28]
14:29:38 [] Vulcan $ cd ../ghc-linear-types/
✔ ~/Contracts/OSS/Projects/ghc-linear-types [:3ba1e33b7c|✚ 24]
14:29:42 [] Vulcan $ nix-shell '<nixpkgs>' -A haskell.compiler.ghcHEAD
✔ ~/Contracts/OSS/Projects/ghc-linear-types [:3ba1e33b7c|✚ 24]
14:29:45 [] Vulcan $ bulidPhase
bash: bulidPhase: command not found
✔ ~/Contracts/OSS/Projects/ghc-linear-types [:3ba1e33b7c|✚ 24]
14:29:48 [] Vulcan $ buildPhase
make flags: SHELL=/nix/store/ya2d87pibq04jwymyfvggl020wf4148k-bash-4.4-p12/bin/bash
===--- building phase 0
make --no-print-directory -f ghc.mk phase=0 phase_0_builds
make[1]: Nothing to be done for 'phase_0_builds'.
===--- building phase 1
make --no-print-directory -f ghc.mk phase=1 phase_1_builds
make[1]: Nothing to be done for 'phase_1_builds'.
===--- building final phase
make --no-print-directory -f ghc.mk phase=final all
"inplace/bin/ghc-stage2" -hisuf dyn_hi -osuf  dyn_o -hcsuf dyn_hc -fPIC -dynamic  -H32m -O -Wall      -hide-all-packages -i -iutils/haddock/driver -iutils/haddock/haddock-api/src -iutils/haddock/haddock-library/vendor/attoparsec-0.13.1.0 -iutils/haddock/haddock-library/src -iutils/haddock/dist/build -Iutils/haddock/dist/build -iutils/haddock/dist/build/haddock/autogen -Iutils/haddock/dist/build/haddock/autogen    -optP-DIN_GHC_TREE -optP-include -optPutils/haddock/dist/build/haddock/autogen/cabal_macros.h -package-id base-4.10.0.0 -package-id filepath-1.4.1.2 -package-id directory-1.3.0.2 -package-id containers-0.5.10.2 -package-id deepseq-1.4.3.0 -package-id array-0.5.1.2 -package-id xhtml-3000.2.2 -package-id Cabal-2.0.0.0 -package-id ghc-boot-8.2.0.20170705 -package-id ghc-8.2.0.20170705 -package-id bytestring-0.10.8.2 -package-id transformers-0.5.2.0 -funbox-strict-fields -Wall -fwarn-tabs -O2 -threaded -XHaskell2010  -no-user-package-db -rtsopts -Wno-unused-imports -Wno-deprecations     -Wnoncanonical-monad-instances  -odir utils/haddock/dist/build -hidir utils/haddock/dist/build -stubdir utils/haddock/dist/build    -c utils/haddock/haddock-api/src/Haddock/Utils.hs -o utils/haddock/dist/build/Haddock/Utils.dyn_o

utils/haddock/haddock-api/src/Haddock/Utils.hs:188:53: error:
    • Couldn't match type ‘GenLocated SrcSpan (BangType Name)’
                     with ‘Weight.Weighted (LBangType Name)’
      Expected type: HsConDeclDetails Name
        Actual type: HsConDetails
                       (LBangType Name) (Located [LConDeclField Name])
    • In the ‘con_details’ field of a record
      In the first argument of ‘Just’, namely
        ‘(h98d
            {con_details = PrefixCon (field_types (map unL (unL fields)))})’
      In the expression:
        Just
          (h98d
             {con_details = PrefixCon (field_types (map unL (unL fields)))})
    |
188 |           | otherwise -> Just (h98d { con_details = PrefixCon (field_types (map unL (unL fields))) })
    |                                                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
make[1]: *** [utils/haddock/ghc.mk:21: utils/haddock/dist/build/Haddock/Utils.dyn_o] Error 1
make: *** [Makefile:127: all] Error 2
✔ ~/Contracts/OSS/Projects/ghc-linear-types [:3ba1e33b7c|✚ 24]
14:29:57 [4.874s] Vulcan $
